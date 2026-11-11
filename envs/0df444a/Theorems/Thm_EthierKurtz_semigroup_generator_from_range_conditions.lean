-- Prove2me | Theorems.Thm_EthierKurtz_semigroup_generator_from_range_conditions
-- name    : EthierKurtz.semigroup_generator_from_range_conditions
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:51:23.595877+00:00
-- url     : https://prove2.me/theorems/ef04b712-b982-4a11-8512-d6cdf9c746dd
-- title:
--   Dissipative range conditions generate the characterization semigroup
-- statement:
--   Under the dissipativity and dense range assumptions of the martingale characterization theorem, construct a strongly continuous contraction semigroup on L whose generator is the closure of A-prime.

import Definitions.Def_auto_M04_6e37b463_UniformBoundedFunction
import Definitions.Def_auto_M04_6e37b463_processPast
import Definitions.Def_auto_M04_6e37b463_SolvesMartingaleProblem

open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology

theorem EthierKurtz.semigroup_generator_from_range_conditions
    {E : Type*}
    (A A' : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E))
    (hsub : A' ≤ A)
    (hdiss : ∀ fg ∈ A, ∀ a : ℝ, 0 < a →
      a * ‖fg.1‖ ≤ ‖a • fg.1 - fg.2‖)
    (L : Submodule ℝ (UniformBoundedFunction E))
    (hrange : ∃ a : ℝ, 0 < a ∧
      closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        a • fg.1 - fg.2) '' (A' : Set _)) = (L : Set _) ∧
      closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        fg.1) '' (A' : Set _)) = (L : Set (UniformBoundedFunction E))) :
    ∃ T : ℝ → L →L[ℝ] L,
      (T 0 = ContinuousLinearMap.id ℝ L ∧
       (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t)) ∧
       (∀ t : ℝ, 0 ≤ t → ‖T t‖ ≤ 1) ∧
       (∀ f : L, Tendsto (fun t : ℝ => T t f) (𝓝[>] (0 : ℝ)) (𝓝 f))) ∧
      (∀ f g : L,
        Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[>] (0 : ℝ)) (𝓝 g) ↔
          (f.val, g.val) ∈ closure (A' : Set _)) := by sorry
