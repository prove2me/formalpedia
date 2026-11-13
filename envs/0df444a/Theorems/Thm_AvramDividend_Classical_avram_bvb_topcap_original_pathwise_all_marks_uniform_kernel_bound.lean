-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_pathwise_all_marks_uniform_kernel_bound
-- name    : AvramDividend.Classical.avram_bvb_topcap_original_pathwise_all_marks_uniform_kernel_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:43:44.332976+00:00
-- url     : https://prove2.me/theorems/9abb3b39-b0ac-4e54-bc72-d209cc26353d
-- title:
--   Original top-cap finite-activity source stopped negative-mark kernel uniformly bounded on almost every complete path
-- statement:
--   At every original path except a P-null set, the full strict discounted negative-mark kernel H n is bounded by a deterministic K simultaneously for every grid cutoff n, every nonnegative time including zero, and every real mark. The mask vanishes on positive marks, outside the strict T cutoff, after ruin, or for negative reserve. On its mask, the Proved finite-horizon original reserve and mark-loss bound applies. No finite dividend cap is needed.
-- source:
--   Direct corollary of Proved original finite-horizon discounted negative-mark bound 6b6d3ac9 and the strict preterminal mask. Intermediate for occupation-product a.e. bound b7f7a6c5; critical to signed mark compensation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_topcap_original_pathwise_all_marks_uniform_kernel_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCapTop : C = ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ t : ℝ≥0, ∀ z : ℝ,
        |H n ((t, ω), z)| ≤ K := by sorry
