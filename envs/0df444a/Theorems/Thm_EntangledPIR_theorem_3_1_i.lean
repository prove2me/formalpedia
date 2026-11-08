-- Prove2me | Theorems.Thm_EntangledPIR_theorem_3_1_i
-- name    : EntangledPIR.theorem_3_1_i
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:11:55.235209+00:00
-- url     : https://prove2.me/theorems/6710f127-8920-4f0d-9d85-944c4ffb61b0
-- title:
--   Theorem 3.1(i) — cut-and-choose against coherent attacks
-- statement:
--   Let $k,d\ge1$ and $\ell\ge2$, and suppose that the projectors $\Pi_{i,j}$ on the copies satisfy (3.1). Let $\lambda\ge0$ be an integer. If the sharing $(\mu_x)_{x\in\mathcal X}$ has privacy threshold $\lambda$, then for every register $\mathsf R$, every subnormalized state $\rho$ of $\mathsf{RB}$, and all $x,x'\in\mathcal X$,
--
--   $$D(\zeta_x,\zeta_{x'})\le\sum_{s+s'>\lambda}\ell^{-(s+s')/2}\sqrt{p_sp_{s'}}\le\frac{\ell^{-(\lambda+1)/2}}{1-\ell^{-1/2}}\,\mathrm{Tr}\,\rho,$$
--
--   the sum over $s,s'\in\{0,\dots,k\}$, where $\zeta_x=R_x(A(\rho))$ is the subnormalized state on acceptance of $\mathsf R$ and the classical registers holding $t$ and $K$. The bound holds for general tests and sharings and does not depend on $k$, $d$ or $\mathsf R$. For $\ell=4$ its right side is $2^{-\lambda}\mathrm{Tr}\,\rho$.
--
--   Differences from the source:
--   - encoding: finite-dimensional registers and tensor products → finite basis types, `Matrix` on them and `⊗ₖ`; reason: Lean convention; a register is its computational basis, same operators
--   - encoding: $\{0,1\}^d$ and $\oplus$ → `Fin d → Bool` and coordinatewise `xor`; reason: Lean convention; same strings
--   - encoding: $\zeta_x$, the state of the procedure (1)–(3) on acceptance → `Rmap (mu x) (Amap Pi ρ)`; reason: $\zeta_x=R_x(A(\rho))$ on p.16
--   - encoding: a subnormalized state → $\rho$ positive semidefinite with `ρ.trace.re ≤ 1`; reason: Hermitian, so its trace is real; $\mathrm{Tr}\,\rho$ as a real part
--   - encoding: the secrets form a finite set; the distributions $\mu_x$ → `[Fintype X]`, and `IsShareDistribution mu` with `mu x y : ℝ`; reason: Lean convention
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Theorem 3.1(i), p.12

import Definitions.Def_EntangledPIR_CutChoose
import Definitions.Def_DimFreeShadow_traceDistance

open Matrix
open scoped ComplexOrder

namespace EntangledPIR

/-- **Theorem 3.1(i) (Cut-and-Choose against Coherent Attacks)**, Mantri, manuscript (Nov. 2026), p.12. Suppose
that (3.1) holds. Let `λ ≥ 0`. If the sharing has privacy threshold `λ`, then for every register `R`, every
subnormalized state `ρ` of `RB`, and all `x, x′`,
`D(ζ_x, ζ_{x′}) ≤ ∑_{s+s′>λ} ℓ^{-(s+s′)/2} √(p_s p_{s′}) ≤ (ℓ^{-(λ+1)/2} / (1 − ℓ^{-1/2})) Tr ρ`, (3.2), the sum over
`s, s′ ∈ {0, …, k}`, with `ζ_x = R_x(A(ρ))`, p.16, the state on acceptance. Part (ii) of the theorem is a
separate statement that the mission does not formalize. -/
theorem theorem_3_1_i {k ℓ d : ℕ} (hk : 1 ≤ k) (hd : 1 ≤ d) (hℓ : 2 ≤ ℓ) {E : Fin k × Fin ℓ → Type}
    [∀ c, Fintype (E c)] [∀ c, DecidableEq (E c)]
    (Pi : ∀ c, Matrix (CopyB d E c) (CopyB d E c) ℂ) (hPi : IsTestFamily Pi)
    (lam : ℕ) {X : Type} [Fintype X] (mu : X → ShareVec k d → ℝ) (hmu : IsShareDistribution mu)
    (hthr : HasPrivacyThreshold mu lam)
    {R : Type} [Fintype R] [DecidableEq R] (ρ : Matrix (R × AllB d E) (R × AllB d E) ℂ)
    (hρ : ρ.PosSemidef) (hρ1 : ρ.trace.re ≤ 1) (x x' : X) :
    DimFreeShadow.traceDistance (Rmap (R := R) (mu x) (Amap Pi ρ)) (Rmap (R := R) (mu x') (Amap Pi ρ)) ≤
        ∑ s ∈ Finset.range (k + 1), ∑ s' ∈ Finset.range (k + 1),
          (if lam < s + s' then
            (ℓ : ℝ) ^ (-((s : ℝ) + (s' : ℝ)) / 2) * Real.sqrt (probS Pi ρ s * probS Pi ρ s')
          else 0) ∧
      (∑ s ∈ Finset.range (k + 1), ∑ s' ∈ Finset.range (k + 1),
          (if lam < s + s' then
            (ℓ : ℝ) ^ (-((s : ℝ) + (s' : ℝ)) / 2) * Real.sqrt (probS Pi ρ s * probS Pi ρ s')
          else 0)) ≤
        (ℓ : ℝ) ^ (-((lam : ℝ) + 1) / 2) / (1 - (ℓ : ℝ) ^ (-(1 : ℝ) / 2)) * ρ.trace.re := by sorry

end EntangledPIR
