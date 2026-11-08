-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian18_original_gradient_elementary_L2_sequence
-- name    : AvramDividend.Classical.avram_ubv_gaussian18_original_gradient_elementary_L2_sequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T21:53:23.434201+00:00
-- url     : https://prove2.me/theorems/3b348621-653b-4c46-8b0c-741c72cfaa52
-- title:
--   Construct original prepayment Gaussian coefficient L² approximants from adapted elementary rectangles
-- statement:
--   For the actual original Avram Levy path, original right-continuous predictable filtration and left-limit prepayment reserve, construct a concrete sequence of finite real linear combinations of adapted time-zero and future-rectangle indicators whose L² coefficients converge to the actual clipped Gaussian gradient. This bridges the separately Proved original gradient square-integrability and predictable rectangle density theorems, permitting an elementary Gaussian stochastic integral to be defined by completion on the same sample space. It does not assume or assert an Ito identity or a Gaussian decomposition.
-- source:
--   Proved original gradient MemLp 498f21c8 and original predictable rectangle L2 density d66ba67a; sequential closure in pinned Mathlib.Topology.Sequences. Feeds the original P4 source witness fdb9a6a3 without replacing its process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian17_original_masked_gradient_MemLp
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_elementary_predictable_L2_dense

open MeasureTheory Set Filter TopologicalSpace AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian18_original_gradient_elementary_L2_sequence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    [IsFiniteMeasure μ] (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let G : ℝ≥0 × Ω → ℝ := fun p =>
      X.σ * (if Y p ∈ Icc u v then deriv w (Y p) else 0)
    let T : Set (Set (ℝ≥0 × Ω)) :=
      {A | (∃ B : Set Ω, MeasurableSet[𝓕.rightCont 0] B ∧
                 A = ({0} ×ˢ B)) ∨
           (∃ t : ℝ≥0, ∃ B : Set Ω, MeasurableSet[𝓕.rightCont t] B ∧
                 A = (Ioi t ×ˢ B))}
    let S : Set (Lp ℝ (2 : ℝ≥0∞) μ) :=
      {z | ∃ (A : Set (ℝ≥0 × Ω))
          (hA : A ∈ insert univ (insert ∅ T))
          (hm : MeasurableSet[𝓕.rightCont.predictable] A) (hfinite : μ A ≠ ⊤),
          indicatorConstLp (2 : ℝ≥0∞) hm hfinite (1 : ℝ) = z}
    ∃ e : ℕ → Lp ℝ (2 : ℝ≥0∞) μ,
      (∀ n, e n ∈ Submodule.span ℝ S) ∧
      Tendsto e atTop (𝓝 ((avram_ubv_gaussian17_original_masked_gradient_MemLp
        X x D hD w a b u v hw hau huv hvb μ hμ).toLp G)) := by sorry
