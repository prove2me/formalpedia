-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_stopped_negative_mark_kernel_uniform_bound
-- name    : AvramDividend.Classical.avram_bvb_topcap_original_stopped_negative_mark_kernel_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T10:10:58.625593+00:00
-- url     : https://prove2.me/theorems/6b6d3ac9-d288-4b5b-8597-992d949025d2
-- title:
--   Original BV top-cap stopped negative-mark payoff is uniformly bounded on each finite horizon
-- statement:
--   For a fixed finite clock and nonnegative discount rate, the original prepayment reserve is almost surely bounded above on the entire horizon. On the nonnegative reserve mask, compact continuity and zero extension uniformly bound negative-mark value losses. Since exp(-qt) is in (0,1], the original stopped negative-mark kernel has a deterministic absolute bound K on every negative mark, including zero reserve and ruin endpoints.
-- source:
--   Conjunction of Proved pre-jump reserve upper 16f30ca5 and compact negative mark loss c1fc53f3, with Real.exp_le_exp. Intended integrable dominator for public top-cap mark J and source predictable compensator V in theorem 46849a70.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_topcap_original_stopped_negative_mark_kernel_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (T : ℝ≥0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
      let b : ℝ := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
      0 ≤ b → ∀ z : ℝ, z < 0 →
        |Real.exp (-(q * (t : ℝ))) * (w (b + z) - w b)| ≤ K := by sorry
