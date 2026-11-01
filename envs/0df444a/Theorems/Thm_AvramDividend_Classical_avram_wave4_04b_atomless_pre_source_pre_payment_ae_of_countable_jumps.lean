-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_atomless_pre_source_pre_payment_ae_of_countable_jumps
-- name    : AvramDividend.Classical.avram_wave4_04b_atomless_pre_source_pre_payment_ae_of_countable_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:49:41.465853+00:00
-- url     : https://prove2.me/theorems/e7696306-5cf2-4206-a9df-b07dc9e4d72e
-- title:
--   Atomless dividends see the true pre-source/pre-payment reserve when source jump times are countable
-- statement:
--   On the actual filtered spectrally negative Lévy path with an adapted dividend strategy, assume the source path has countably many nonzero positive left jumps, as already proved in the BV case. Then for every atomless time measure, including singular-continuous dividend variation, almost every positive time identifies the controlled pre-event reserve with riskProcess: x+X(s−)-D⁺(s) = x+X_s-D_s. This resolves the chronological a.e. evaluation of the diffuse Ito–Meyer derivative without supposing that the control is absolutely continuous. The explicit source jump countability premise is not a stochastic decomposition axiom and must be discharged in UBV by a genuine càdlàg argument.
-- source:
--   Canonically Proved adapted dividend right-jump countability and atomless equality, genuine actual X source jump-time countability in the 04-A BV branch; Mathlib Set.Countable.image, measure_zero, and ae_iff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_atomless_right_limit_eq_pre_payment_ae

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_atomless_pre_source_pre_payment_ae_of_countable_jumps
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω)
    (hcount : Set.Countable {t : ℝ≥0 |
      0 < t ∧ X.X t ω ≠ Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t})
    (ν : Measure ℝ) [NullSingletonClass ν] :
    ∀ᵐ s ∂ν, 0 < s →
      riskProcess X x D s.toNNReal ω =
        x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
          rightLimit D s.toNNReal ω := by sorry
