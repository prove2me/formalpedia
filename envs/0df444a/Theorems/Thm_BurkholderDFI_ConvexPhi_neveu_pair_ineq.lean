-- Prove2me | Theorems.Thm_BurkholderDFI_ConvexPhi_neveu_pair_ineq
-- name    : BurkholderDFI.ConvexPhi.neveu_pair_ineq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:07.222673+00:00
-- url     : https://prove2.me/theorems/89804eed-bab7-4d6f-a54f-a840cc3732e8
-- title:
--   §16 — Neveu's pair inequality (cited)
-- statement:
--   Let $z_k$ be nonnegative measurable random variables and let
--   $$
--   W=\sum_{k\ge1}E(z_k\mid\mathcal A_{k-1}),\qquad
--   Z=\sum_{k\ge1}z_k.
--   $$
--   Neveu's cited inequality states that, for every $\lambda>0$,
--   $$
--   \int_{\{W>\lambda\}}(W-\lambda)\,dP
--   \le\int_{\{W>\lambda\}}Z\,dP.
--   $$
--   This is the pair estimate used to establish Lemma 16.1.
--
--   **Formalization Note** The $z_k$ need only be measurable in the ambient sigma field; no adaptedness is assumed. All sums, conditional expectations, and integrals are extended nonnegative.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), §16, proof of Lemma 16.1, p. 34 (Neveu [33], [30])

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.ConvexPhi
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- §16, p. 34: Neveu's cited pair inequality. -/
theorem neveu_pair_ineq {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (z : ℕ → Ω → ℝ≥0∞) (hz : ∀ k, Measurable (z k)) :
    ∀ l : ℝ, 0 < l →
      (∫⁻ ω in {ω | ENNReal.ofReal l <
        ∑' k : ℕ, condLExp (ℱ k) P (z (k + 1)) ω},
        ((∑' k : ℕ, condLExp (ℱ k) P (z (k + 1)) ω) - ENNReal.ofReal l) ∂P)
      ≤ (∫⁻ ω in {ω | ENNReal.ofReal l <
        ∑' k : ℕ, condLExp (ℱ k) P (z (k + 1)) ω},
        (∑' k : ℕ, z (k + 1) ω) ∂P) := by sorry
end BurkholderDFI.ConvexPhi
