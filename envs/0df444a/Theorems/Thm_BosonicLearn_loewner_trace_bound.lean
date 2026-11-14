-- Prove2me | Theorems.Thm_BosonicLearn_loewner_trace_bound
-- name    : BosonicLearn.loewner_trace_bound
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T06:56:46.619208+00:00
-- url     : https://prove2.me/theorems/1125bb57-59fe-4ab7-a10b-5eab2d6c2479
-- title:
--   $0\preceq D\preceq cS\ \Rightarrow\ \mathrm{Tr}(S^{-1}DS^{-1}D)\le c^2d$ (relative Frobenius bound)
-- statement:
--   A Loewner sandwich bounds the relative Frobenius norm.
--
--   Let $S$ be a real positive definite $d\times d$ matrix, $c\ge0$, and $D$ a real symmetric matrix with $0\preceq D\preceq c\,S$. Then
--
--   $$
--   \big\|S^{-1/2}DS^{-1/2}\big\|_{\mathrm F}^2=\operatorname{Tr}\big(S^{-1}DS^{-1}D\big)\le c^2\,d .
--   $$
--
--   Role. In the proof of Theorem 8, $S=\Sigma$, $D=\tilde\Sigma-\Sigma$, $d=2n$ and $c=2\alpha_\nu\zeta/(1-\zeta)$; this is Eq. (215), the bound on the quantity $\Delta_{\mathrm{rel}}$ of Theorem 7.
--
--   **Formalization Note** The squared Frobenius norm is written as the trace $\operatorname{Tr}(S^{-1}DS^{-1}D)$, the form in which `BosonicLearn.theorem_7` states $\Delta_{\mathrm{rel}}^2$. Loewner order is `Matrix.PosSemidef` of the difference; $d$ is `Fintype.card ι`. Pure linear algebra.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Eq. (215), p. 62 (proof of Theorem 8)

import Mathlib

open scoped Matrix

namespace BosonicLearn

/-- **Relative Frobenius bound from a Loewner sandwich.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §7.2, proof of Theorem 8, Eq. (215), p. 62: "0 ⪯ Σ^{−1/2}(Σ̃ − Σ)Σ^{−1/2} ⪯ (2α_ν ζ/(1 − ζ)) I. … Since for a
positive semidefinite matrix ‖R‖_F² is the sum of the squares of its eigenvalues, we obtain
‖Σ^{−1/2}(Σ̃ − Σ)Σ^{−1/2}‖_F ≤ (2α_ν ζ/(1 − ζ)) √(2n)."

Let `S` be a real positive definite `d × d` matrix and `D` a real symmetric matrix with `0 ⪯ D ⪯ c S`, `c ≥ 0`.
Then `‖S^{−1/2} D S^{−1/2}‖_F² = Tr(S⁻¹ D S⁻¹ D) ≤ c² d`.

**Formalization Note.** The squared Frobenius norm is written as `Tr(S⁻¹ D S⁻¹ D)`, the form in which
`theorem_7` states `Δ_rel²`. Loewner order is positive semidefiniteness of the difference. -/
theorem loewner_trace_bound {ι : Type} [Fintype ι] [DecidableEq ι] (S D : Matrix ι ι ℝ) (hS : S.PosDef)
    (hD : D.PosSemidef) (c : ℝ) (hc : 0 ≤ c) (hDS : (c • S - D).PosSemidef) :
    (S⁻¹ * D * S⁻¹ * D).trace ≤ c ^ 2 * Fintype.card ι := by sorry

end BosonicLearn
