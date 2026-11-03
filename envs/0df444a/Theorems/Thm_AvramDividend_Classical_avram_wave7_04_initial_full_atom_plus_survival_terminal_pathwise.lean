-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_04_initial_full_atom_plus_survival_terminal_pathwise
-- name    : AvramDividend.Classical.avram_wave7_04_initial_full_atom_plus_survival_terminal_pathwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:34:52.865577+00:00
-- url     : https://prove2.me/theorems/50981c17-6933-436c-96ca-d1c588725de1
-- title:
--   Original source zero-clock full Stieltjes payment atom plus surviving post-rightpayment terminal is HJB-budgeted pathwise
-- statement:
--   For each original Levy sample path, at the deterministic time-zero stopped clock the real full Stieltjes discounted cash atom plus the nonnegative post-rightpayment HJB terminal value on the strict survival event is at most w(x). Assumes the original right-jump secant dominance and nonnegative value after the permitted initial lump sum. The statement retains the exact source ruinTime, dividendMeasure and paymentTimes, and proves the boundary base of the finite-horizon stopped supermartingale.
-- source:
--   Source-faithful zero-clock base for the stronger full-horizon stopped BV supermartingale 0618723a-bb0b-4fa0-94bc-4def7af7aafa. Direct proof imports Proved W7-02 original initial jump HJB and full atom identity 0315346e-a771-490f-b107-7af330db9139 and Proved original zero-horizon full Stieltjes cash identification 50183965-497e-4b6a-9601-a1cc826ac588. Retains the exact source process and pathwise ruin boundary; no surrogate process or premise claiming the conclusion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_04_initial_full_atom_plus_survival_terminal_pathwise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (hpost : ∀ ω, 0 ≤ w (x - rightLimit D 0 ω))
    (ω : Ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (0 : ℝ≥0∞) < ruinTime X x D ω then
       max 0 (w (x - rightLimit D 0 ω))
     else 0) ≤ w x := by sorry
