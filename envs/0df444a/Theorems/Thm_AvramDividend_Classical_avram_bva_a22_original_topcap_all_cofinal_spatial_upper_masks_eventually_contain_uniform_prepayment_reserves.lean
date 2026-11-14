-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_topcap_all_cofinal_spatial_upper_masks_eventually_contain_uniform_prepayment_reserves
-- name    : AvramDividend.Classical.avram_bva_a22_original_topcap_all_cofinal_spatial_upper_masks_eventually_contain_uniform_prepayment_reserves
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:30:14.826739+00:00
-- url     : https://prove2.me/theorems/96487e5b-488d-4a5a-9e70-8d2e6d65703c
-- title:
--   Original infinite-cap source arbitrary cofinal upper spatial masks eventually contain every actual prepayment reserve up to the horizon almost surely
-- statement:
--   For the genuine original spectrally negative Lévy bounded-variation process X, an actual admissible singular dividend control D and infinite dividend cap, fix the original horizon S. The already Proved source physical drift bound places ALL actual pre-right-payment left-limit reserves before S almost surely below one deterministic upper bound B=max(x+max(S*X.drift,0),0), uniformly over time and path. For any original supplied arbitrary cofinal interior bands a_n,b_n, choose the genuine positive interior reserve y=max(1,B+1). Cofinal coverage then ensures y<=b_n for every sufficiently late original spatial index. Prove that on a single probability-one source event, for every such index, every physical t<=S, the original left-limit controlled reserve is below b_n. The upper mask is therefore eventually redundant uniformly over actual original controlled paths, without selected band nesting or a spatial-versus-physical rate. The lower zero-reserve boundary and stopped marked compensator occupation remain separate original BVA96 obligations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_prejump_reserve_uniform_horizon_upper
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_topcap_all_cofinal_spatial_upper_masks_eventually_contain_uniform_prepayment_reserves
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (hTop : C = ⊤) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (S : ℝ≥0)
    (a b : ℕ → ℝ)
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) :
    ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂P,
      ∀ t : ℝ≥0, t ≤ S →
        Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t ≤ b n := by sorry
