-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb61_original_terminal_source_jump_integral_eventually_zero
-- name    : AvramDividend.Classical.avram_bvb61_original_terminal_source_jump_integral_eventually_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:28:46.6541+00:00
-- url     : https://prove2.me/theorems/5216b7e7-ff3b-49aa-8f5e-d8b77734bb28
-- title:
--   Original finite-activity negative-jump weighted source integral vanishes on the final prescribed uniform strip
-- statement:
--   For the original actual physical spectrally negative Levy jump counting measure with bounded variation and finite negative activity, the terminal uniform-grid strip (T(n+1)/(n+2),T] carries zero jump mass eventually P-almost surely. Consequently every real weight on the original source jump times has exactly zero integral on that strip eventually. No restriction to sample-dependent approximating clocks or substituted jump processes.
-- source:
--   BVB51 Proved original negative-jump count eventual terminal strip vanishing, Avram Proposition 4(i) finite activity proof

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb51_original_uniform_last_horizon_source_negative_count_zero_ae
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb61_original_terminal_source_jump_integral_eventually_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2))
    (g : ℝ≥0 → Ω → ℝ) :
    let S : ℝ≥0 := ⟨T,le_of_lt hT⟩
    ∀ᵐ ω ∂P, ∀ᶠ n in (atTop : Filter ℕ),
      (∫ t in Ioc (u n (n + 1)) S, g t ω
        ∂(Measure.count.restrict
          {t : ℝ≥0 | 0 < t ∧
            X.X t ω - Function.leftLim
              (fun s : ℝ≥0 => X.X s ω) t ≠ 0})) = 0 := by sorry
