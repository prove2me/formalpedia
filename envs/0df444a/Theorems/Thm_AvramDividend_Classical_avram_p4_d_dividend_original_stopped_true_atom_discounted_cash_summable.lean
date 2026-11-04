-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_true_atom_discounted_cash_summable
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_stopped_true_atom_discounted_cash_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:45:33.460269+00:00
-- url     : https://prove2.me/theorems/92982025-c929-4dc2-971f-7f4ea35e51ae
-- title:
--   Actual finite stopped original Stieltjes atomic cash weights are countably and really summable
-- statement:
--   At the actual source-original finite horizon T with the exact ruinTime paymentTimes selector, the previously proved full stopped Stieltjes cash decomposition expresses the nonnegative discounted atom sum plus a nonnegative atomless integral, bounded by ENNReal.ofReal(rightLimit D T). Therefore that actual weighted atomic ENNReal sum is finite, and its toReal terms form an honestly summable real series. The countable atom carrier contains every nonzero original restricted dividend measure singleton. This keeps time-zero and surviving horizon atoms and excludes positive ruin atom by the exact payment selector; diffuse including singular-continuous cash remains separately in the original decomposition.
-- source:
--   Avram–Palmowski–Pistorius Prop 4(i), Eq 5.13; source-proved 0a519d31 full original stopped actual discounted atom/diffuse cash bound; Mathlib ENNReal.summable_toReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_stopped_discounted_all_atoms_diffuse_cash_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_stopped_true_atom_discounted_cash_summable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ A : Set ℝ,
      A.Countable ∧
      (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) ∧
      Summable (fun t : A =>
        (μ {(t : ℝ)} *
          (if (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)
            then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
            else 0)).toReal) := by sorry
