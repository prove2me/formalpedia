-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise17_original_finite_simple_mark_condexp_zero
-- name    : AvramDividend.Classical.avram_anoise17_original_finite_simple_mark_condexp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T00:33:29.834555+00:00
-- url     : https://prove2.me/theorems/6de0a6db-7bab-49a8-ab0a-220ed0e04fac
-- title:
--   Original-filtration conditional centring of finite simple marked-jump sums
-- statement:
--   Finite linear combinations of genuine original marked-jump counts, each compensated by its original Levy intensity, have zero conditional expectation in the original right-continuous filtration at the left endpoint. This is a finite-simple-function source step towards the bounded intrinsic small-jump compensator and its stopped martingale limit.
-- source:
--   Avram classical dividend finite-activity intrinsic compensated jump source; source path marked measure on original Omega and original filtration. Derive from proved finite-band conditional count centring b821b059 and integrability, then finite-sum conditional-expectation linearity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_source_finite_band_rightCont_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_real_integrable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise17_original_finite_simple_mark_condexp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (r : ℕ → ℝ≥0)
    (hsr : ∀ n, s < r n) (hrt : ∀ n, r n ≤ t)
    (hShort : Tendsto (fun n => r n - s) atTop (𝓝 0))
    (hLong : Tendsto (fun n => t - r n) atTop (𝓝 (t - s)))
    (S : Finset ι) (B : ι → Set ℝ)
    (hB : ∀ i ∈ S, MeasurableSet (B i))
    (hFinite : ∀ i ∈ S, X.ν (B i) ≠ ⊤)
    (J : ι → ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞)
    (hJsource : ∀ i ∈ S, ∀ a b ω,
      J i a b ω =
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc a b ×ˢ B i))
    (hJmeas : ∀ i ∈ S, Measurable (J i s t))
    (weights : ι → ℝ) :
    P[(fun ω => ∑ i ∈ S, weights i *
      ((J i s t ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal)) |
        𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ)) := by
  sorry
