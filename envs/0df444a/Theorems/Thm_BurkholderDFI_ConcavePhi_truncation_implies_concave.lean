-- Prove2me | Theorems.Thm_BurkholderDFI_ConcavePhi_truncation_implies_concave
-- name    : BurkholderDFI.ConcavePhi.truncation_implies_concave
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:15:15.638899+00:00
-- url     : https://prove2.me/theorems/d25bf0b6-b933-4bde-83d7-d7ed2cd4f3e6
-- title:
--   §20, proof of Theorem 20.1 — the truncated inequality (20.2) implies EΦ(Z) ≤ 2EΦ(W) for every concave Φ
-- statement:
--   Let $(\Omega,\mathcal A,P)$ be a probability space and $Z,W$ measurable functions on $\Omega$ with values in $[0,\infty]$. Let $\Phi:[0,\infty]\to[0,\infty]$ be non-decreasing, continuous, with $\Phi(0)=0$, satisfying the growth condition $\Phi(2\lambda)\le c\,\Phi(\lambda)$ for some constant $c$, and concave on $[0,\infty)$. If
--   $$E(Z\wedge\lambda)\le 2E(W\wedge\lambda)\qquad\text{for every }\lambda>0,$$
--   then
--
--   $$E\Phi(Z)\le 2E\Phi(W).$$
--
--   The paper states this as "Inequality (20.2) is a special case of (20.1) but actually implies (20.1)", for the particular $Z=\sum z_k$ and $W=\sum E(z_k\mid\mathcal A_{k-1})$ of Theorem 20.1. Its argument uses nothing about $Z$ and $W$ beyond (20.2), so the implication is stated here for arbitrary $Z$ and $W$. It reduces Theorem 20.1 to the one-parameter family $\Phi(t)=t\wedge\lambda$.
--
--   **Formalization Note** "Concave as above" is the pair `IsPhi Φ c` (for an arbitrary constant `c`; concavity in fact gives $c=2$) and `IsConcavePhi Φ`. Expectations are Lebesgue integrals of $[0,\infty]$-valued functions; $\lambda$ ranges over positive reals (`l : ℝ≥0`).
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), §20, proof of Theorem 20.1, p. 38

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BurkholderDFI.ConcavePhi

/-- §20, proof of Theorem 20.1, p. 38: "Inequality (20.2) is a special case of (20.1) but actually
implies (20.1)." Stated for arbitrary measurable `[0, ∞]`-valued `Z`, `W`: if
`E(Z ∧ λ) ≤ 2E(W ∧ λ)` for every `λ > 0`, then `EΦ(Z) ≤ 2EΦ(W)` for every concave `Φ` satisfying
the conditions of Section 7. -/
theorem truncation_implies_concave {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (Φ : ℝ≥0∞ → ℝ≥0∞) (c : ℝ≥0) (hΦ : BurkholderDFI.SquareFnLp.IsPhi Φ c)
    (hcc : BurkholderDFI.SquareFnLp.IsConcavePhi Φ) (Z W : Ω → ℝ≥0∞) (hZ : Measurable Z) (hW : Measurable W)
    (h202 : ∀ l : ℝ≥0, 0 < l →
      ∫⁻ ω, min (Z ω) (l : ℝ≥0∞) ∂P ≤ 2 * ∫⁻ ω, min (W ω) (l : ℝ≥0∞) ∂P) :
    ∫⁻ ω, Φ (Z ω) ∂P ≤ 2 * ∫⁻ ω, Φ (W ω) ∂P := by sorry

end BurkholderDFI.ConcavePhi
