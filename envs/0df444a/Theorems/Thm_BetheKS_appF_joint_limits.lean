-- Prove2me | Theorems.Thm_BetheKS_appF_joint_limits
-- name    : BetheKS.appF_joint_limits
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:38:21.194218+00:00
-- url     : https://prove2.me/theorems/3e517d19-2242-4dbc-93fd-3cde8516242c
-- title:
--   App. F (joint limits), p.26 — $\sum_{i\ge2,|\mu_i|>\sqrt d}\|U_n^{\mathsf T}X_i/\sqrt n\|_2^2\ge S-o_{\mathbb P}(1)$
-- statement:
--   Let $c$ have the projection property of Theorem 2.2 and $S=\sum_{i\ge2,|\mu_i|>\sqrt d}c_{\mu_i}^2$. Let $(\mu_i,\phi_i)$ be a planted eigenbasis and $X_i=\phi_i\circ\sigma$. Let $E_n$ be the sum of all informative outlier subspaces of $H(\sqrt d,G_n)$ and $H(-\sqrt d,G_n)$, and $U_n\in\mathbb R^{n\times m}$ an orthonormal basis of $E_n\cap\mathbf 1^\perp$. Then
--   $$
--   \sum_{i\ge2,\ |\mu_i|>\sqrt d}\Big\|U_n^{\mathsf T}\frac{X_i}{\sqrt n}\Big\|_2^2\ \ge\ S-o_{\mathbb P}(1):
--   $$
--   for every $\varepsilon>0$, with probability tending to one, $\dim(E_n\cap\mathbf 1^\perp)=m$ and the left side is at least $S-\varepsilon$.
--
--   This is the step of the proof of Theorem 2.3 that combines Propositions 7.1 and 7.2: the combined outlier basis has a diagonal limiting correlation matrix with the planted directions, and intersecting with $\mathbf 1^\perp$ removes only the constant planted direction.
--
--   Differences from the source:
--
--   - encoding: n → ∞ with |σ⁻¹(i)| = π_i n → n → ∞ along 𝒩_π = {n : π_i n ∈ ℕ ∀ i}, for every sequence of exact-size label maps σ_n; reason: the paper's deterministic community-size convention (p.4); the statement is uniform over the labelings
--   - encoding: π a distribution on [r] → every π_a > 0; reason: the r eigenfunctions orthonormal in L²(π) that the paper uses exist only then; excludes undefined cases
--   - encoding: edge probability P_{σ(u)σ(v)}/n → min(1, P_{σ(u)σ(v)}/n); reason: affects only finitely many n, not the limits
--   - reading: the outlier eigenvectors of H(±√d, G_n) → every choice of increasing orthonormal eigenbases of H(±√d, G), fixed for each graph before the probability; reason: the eigenvectors are unique only up to rotations within repeated eigenvalues; the universal reading is the stronger one
--   - reading: U_n an orthonormal basis of E_n ∩ 1^⊥ in ℝ^{n×m} → the event also asserts dim(E_n ∩ 1^⊥) = m, and U_n is any orthonormal basis of that space when it has dimension m; reason: the paper presupposes the dimension when it chooses U_n ∈ ℝ^{n×m}
--   - reading: S built from the constants of Theorem 2.2 → S built from any family c with the projection property; reason: App. F uses only that property of c (paper.md decision 2)
--   - encoding: ≥ S − o_P(1) → for every ε > 0, P(… ≥ S − ε) → 1; reason: the meaning of o_P(1) in a lower bound
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), App. F, proof of Theorem 2.3, p.26 (PDF p.27), display "The joint limits in Propositions 7.1 and 7.2 give"

import Mathlib
import Definitions.Def_BetheKS_HasProjProperty
import Definitions.Def_BetheKS_roundingAlg

set_option autoImplicit false

namespace BetheKS

/-- **App. F, proof of Theorem 2.3 (joint limits)** — Dong, McKenzie, arXiv:2610.41802 (held version,
sha256 4da41e16…), p.26 (PDF p.27): "The joint limits in Propositions 7.1 and 7.2 give
`∑_{i≥2, |µᵢ|>√d} ‖Uₙᵀ Xᵢ/√n‖²₂ ≥ S − o_P(1)`."

For every family `c` with the projection property of Theorem 2.2, every planted eigenbasis
`(µᵢ, ϕᵢ)`, every exact-size labeling sequence, every choice of increasing eigenbases of `H(±√d, G)`
and every choice of orthonormal basis `Uₙ` of `Eₙ ∩ 1^⊥`, and every `ε > 0`: with probability tending
to one, `dim(Eₙ ∩ 1^⊥) = m` and `∑_{i ≥ 2, |µᵢ| > √d} ∑ₖ (⟨Uₙ,ₖ, Xᵢ⟩/√n)² ≥ S − ε`.

**Formalization Note.** Index `0 : Fin r` is the paper's `i = 1`. The event includes
`dim(Eₙ ∩ 1^⊥) = m`, which the paper presupposes when it chooses `Uₙ ∈ ℝ^{n×m}`. -/
theorem appF_joint_limits {r : ℕ} (p : SBMParams r) (c : ℝ → ℝ) (hc : HasProjProperty p c)
    (μ : Fin r → ℝ) (ϕ : Fin r → Fin r → ℝ) (hϕ : IsPlantedEigenbasis p μ ϕ)
    (σs : ∀ n : ℕ, Fin n → Fin r) (hσ : IsExactSeq p σs)
    (Bp : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), IncEigenbasis (bh (Real.sqrt p.d) G))
    (Bm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), IncEigenbasis (bh (-Real.sqrt p.d) G))
    (U : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), Fin (mDim p) → EuclideanSpace ℝ (Fin n))
    (hU : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), IsBasisChoice p (Bp n G) (Bm n G) (U n G))
    (ε : ℝ) (hε : 0 < ε) :
    Whp p σs (fun n G =>
      Module.finrank ℝ ↥(allOutliers p (Bp n G) (Bm n G) ⊓ (Submodule.span ℝ {onesVec n})ᗮ) = mDim p ∧
      sumS p c - ε ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin r => i.val ≠ 0 ∧ Real.sqrt p.d < |μ i|),
          ∑ k, (inner ℝ (U n G k) (WithLp.toLp 2 (ϕ i ∘ σs n)) / Real.sqrt n) ^ 2) := by sorry

end BetheKS
