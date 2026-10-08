-- Prove2me | Theorems.Thm_BurkholderDFI_ConcavePhi_eq_20_2
-- name    : BurkholderDFI.ConcavePhi.eq_20_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:13:59.199979+00:00
-- url     : https://prove2.me/theorems/c39fc018-32e0-4eeb-b37d-2b647669a596
-- title:
--   (20.2) — E(Z ∧ λ) ≤ 2E(W ∧ λ) for Z = Σ z_k, W = Σ E(z_k | 𝒜_{k−1})
-- statement:
--   Let $(\Omega,\mathcal A,P)$ be a probability space with sub-$\sigma$-fields $\mathcal A_0\subseteq\mathcal A_1\subseteq\cdots$ of $\mathcal A$, and let $z_1,z_2,\dots$ be nonnegative ($[0,\infty]$-valued) measurable functions on $\Omega$. Put
--   $$Z=\sum_{k=1}^\infty z_k,\qquad W=\sum_{k=1}^\infty E(z_k\mid\mathcal A_{k-1}).$$
--   Then
--
--   $$E(Z\wedge\lambda)\le 2E(W\wedge\lambda),\qquad\lambda>0.$$
--
--   This is Theorem 20.1 for the concave functions $\Phi(t)=t\wedge\lambda$; the proof of Theorem 20.1 shows that this special case already implies the general one.
--
--   **Formalization Note** `z (k+1)` is $z_{k+1}$ and `condLExp (ℱ k) P (z (k+1))` is $E(z_{k+1}\mid\mathcal A_k)$, so the sums run over $k\ge1$ with $z_k$ paired with $\mathcal A_{k-1}$. Conditional expectations are the $[0,\infty]$-valued `condLExp`, defined without integrability; the $z_k$ are $\mathcal A$-measurable and not assumed adapted. $\lambda$ is a positive real (`l : ℝ≥0`).
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), (20.2), proof of Theorem 20.1, p. 38

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BurkholderDFI.ConcavePhi

/-- (20.2), proof of Theorem 20.1, p. 38: `E(Z ∧ λ) ≤ 2E(W ∧ λ)`, `λ > 0`, where
`Z = Σ_{k=1}^∞ z_k` and `W = Σ_{k=1}^∞ E(z_k|𝒜_{k−1})`. Here `z (k+1)` is `z_{k+1}` and
`condLExp (ℱ k) P (z (k+1))` is `E(z_{k+1}|𝒜_k)`. -/
theorem eq_20_2 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) (hz : ∀ k, Measurable (z k))
    (l : ℝ≥0) (hl : 0 < l) :
    ∫⁻ ω, min (∑' k, z (k + 1) ω) (l : ℝ≥0∞) ∂P
      ≤ 2 * ∫⁻ ω, min (∑' k, condLExp (ℱ k) P (z (k + 1)) ω) (l : ℝ≥0∞) ∂P := by sorry

end BurkholderDFI.ConcavePhi
