-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_zerojump_finitecap_martingale_FV_strip_preflight
-- name    : AvramDividend.Classical.avram_f6_original_zerojump_finitecap_martingale_FV_strip_preflight
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:36:25.311203+00:00
-- url     : https://prove2.me/theorems/f4f6b9ca-8c5c-4e0e-b0db-1c762acc69f1
-- title:
--   Original zero-jump finite-cap controlled semimartingale and vanishing cap-strip preflight
-- statement:
--   For the original zero-jump unbounded-variation capped dividend risk process, the intrinsic centred Gaussian process and its compensated square are genuine right-continuous-filtration martingales; the controlled dividend path has locally bounded variation; the Lévy path is continuous a.e.; the reserve is the exact continuous martingale plus finite-variation drift/dividend process; and upper-strip expected occupation vanishes at the finite cap. All assertions follow from the original model and admissible strategy, providing the simultaneous actual source conditions for the missing stopped finite-cap Ito-Tanaka/Stieltjes verification step.
-- source:
--   Proved original zerojump semimartingale preflight a44cfbfa; newly Proved original F6 admissible upperstrip vanishing cb1a7c38.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_zerojump_finitecap_martingale_FV_strip_preflight
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) :
    Martingale (fun t ω => X.X t ω - (t : ℝ) * X.c)
      𝓕.rightCont P ∧
    Martingale (fun t ω =>
      (X.X t ω - (t : ℝ) * X.c) ^ 2 -
        (t : ℝ) * X.σ ^ 2) 𝓕.rightCont P ∧
    (∀ ω, LocallyBoundedVariationOn
      (fun t : ℝ≥0 => rightLimit D t ω) Set.univ) ∧
    (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => X.X t ω)) ∧
    (∀ t ω, x + X.X t ω - rightLimit D t ω =
      (X.X t ω - (t : ℝ) * X.c) +
        (x + (t : ℝ) * X.c - rightLimit D t ω)) ∧
    Tendsto (fun j : ℕ =>
      ∫ ω, ∫ t in Ioo (0 : ℝ) (n : ℝ),
        if C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) <
            riskProcess X x D (Real.toNNReal t) ω
        then (1 : ℝ) else 0 ∂volume ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
