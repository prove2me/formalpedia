-- Prove2me | Theorems.Thm_BSCvsBEC_Supplement_theorem_2_6
-- name    : BSCvsBEC.Supplement.theorem_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:36:11.435707+00:00
-- url     : https://prove2.me/theorems/52d94489-c6e6-4f5c-b4bb-80ee3b73bc15
-- title:
--   Theorem 2.6 — qSC/qPSC duality: $F^\dagger\Gamma F=D=\mathrm{diag}(P_V)$
-- statement:
--   Let $\mathbb F_q$ be a finite field, $\mathcal C\le\mathbb F_q^n$ a linear code of dimension $k$ with generator matrix $G\in\mathbb F_q^{k\times n}$, $K=q^k$, and $0\le\theta\le\pi/2$, $\rho=\cos\theta$. Let $X$ be uniform on $\mathcal C$ and sent through $\mathrm{qPSC}_\theta$, let $\Gamma$ be the normalized Gram matrix $\langle u|\Gamma|u'\rangle=\frac1K\langle\varphi_u|\varphi_{u'}\rangle$ of the output states $|\varphi_u\rangle=|\omega_{G^\top u}\rangle$, and let $P_V$ be the distribution of the syndrome $V=GY^\perp$ of $Y^\perp=\mathrm{qSC}_p(X^\perp)$, $X^\perp$ uniform on $\mathcal C^\perp$, $p=\frac{q-1}q(1-\rho)$. With $F=F_k$ the Fourier transform matrix,
--   $$F^\dagger\Gamma F=D=\mathrm{diag}(P_V);$$
--   i.e., the eigenvalues of $\Gamma$ are precisely $(P_V(v))_{v\in\mathbb F_q^k}$.
--
--   Since $\mathrm{spec}(\sigma_Y)=\mathrm{spec}(\Gamma)\cup\{0\}$, the syndrome probabilities of $\mathcal C^\perp$ over $\mathrm{qSC}_p$ are exactly the nonzero eigenvalues of the output state of $\mathcal C$ over $\mathrm{qPSC}_\theta$. This is the duality used in §§3 and 5.
--
--   **Formalization Note** The statement holds for every generator matrix, every nontrivial additive character and every $\mathrm{qPSC}_\theta$ family; the eigenvalue clause is the identity $\det(X-\Gamma)=\prod_v(X-P_V(v))$.
--
--   Differences from the source:
--   - encoding: a nontrivial additive homomorphism ζ : F_q → Z_p and χ_z(y) = exp(2πi ζ(z·y)/p) → a nontrivial additive character ψ : F_q → ℂ and χ_z(y) = ψ(z ⬝ᵥ y); reason: the two families of characters coincide
--   - encoding: Γ's eigenvalues are precisely (P_V(v))_v → charpoly Γ = ∏_v (X − P_V(v)); reason: eigenvalues with multiplicity
--   - encoding: a linear code 𝒞 of dimension k with generator matrix G (Gᵀ a parity-check matrix of 𝒞⊥) → a matrix G ∈ F^{k×n} with u ↦ Gᵀu injective, 𝒞 = codeOf G; reason: every k-dimensional code with every generator matrix arises this way, and conversely
--   - reading: some fixed pure states (|ω_x⟩) in the q-dimensional 𝒴 with ⟨ω_x|ω_x'⟩ = cos θ for x ≠ x' → every such family of unit vectors in ℂ^q (IsQPSCOn θ ω); reason: the page fixes an arbitrary such family; the statement is required for each one
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), Theorem 2.6, eq. (46), p.10 (notation of eqs. (40)–(45), pp.9–10)

import Mathlib
import Definitions.Def_BSCvsBEC_Supplement_syndromePMF

open scoped Matrix

namespace BSCvsBEC.Supplement

/-- **Theorem 2.6 (p.10).** With the notation of §2.4.1 and `F = F_k` the Fourier transform matrix,
`F†ΓF = D` (eq. (46)); i.e., `Γ`'s eigenvalues are precisely `(P_V(v))_{v∈F_q^k}`.
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), Theorem 2.6, eq. (46), p.10, with the notation of eqs. (40)–(45), pp.9–10.

**Formalization Note.** For every finite field `F = F_q`, every `k, n`, every `G ∈ F_q^{k×n}` with
`u ↦ Gᵀu` injective (a generator matrix of the `k`-dimensional code `𝒞 = codeOf G`), every
nontrivial additive character `ψ` (the page's `χ`), every `θ ∈ [0, π/2]` and every `qPSC_θ` family
`ω` in `ℂ^q`. `D = diag(P_V)` with `P_V = syndromePMF G (cos θ)`. The "i.e." clause is the second
conjunct: the characteristic polynomial of `Γ` is `∏_v (X − P_V(v))` (eigenvalues with
multiplicity). -/
theorem theorem_2_6 {F : Type} [Field F] [Fintype F] [DecidableEq F] {k n : ℕ}
    (G : Matrix (Fin k) (Fin n) F) (hG : Function.Injective (Gᵀ.mulVec))
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2)
    (ω : F → EuclideanSpace ℂ (Fin (Fintype.card F))) (hω : IsQPSCOn θ ω) :
    (fourierMat ψ k)ᴴ * gramMat ω G * fourierMat ψ k =
        Matrix.diagonal (fun v => ((syndromePMF G (Real.cos θ) v : ℝ) : ℂ)) ∧
      (gramMat ω G).charpoly =
        ∏ v, (Polynomial.X - Polynomial.C ((syndromePMF G (Real.cos θ) v : ℝ) : ℂ)) := by sorry

end BSCvsBEC.Supplement
