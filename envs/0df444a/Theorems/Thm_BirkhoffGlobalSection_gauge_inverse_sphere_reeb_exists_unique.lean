-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_gauge_inverse_sphere_reeb_exists_unique
-- name    : BirkhoffGlobalSection.gauge_inverse_sphere_reeb_exists_unique
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:13:04.004991+00:00
-- url     : https://prove2.me/theorems/73d8a040-e210-42d4-a3ee-a6ee1bee6144
-- title:
--   Gauge inverse sphere reeb exists unique
-- statement:
--   The squared inverse-gauge weight has a unique sphere Reeb vector when the body contains a neighborhood of zero, is bounded, and its radial chart is smooth at the sphere point.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 4 of the Proved theorem BirkhoffGlobalSection.weighted_reeb_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_weighted_reeb_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_weighted_reeb_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.gauge_inverse_sphere_reeb_exists_unique :
∀ (B : Set Phase)
    (h0 : B ∈ 𝓝 (0 : Phase)) (hb : Bornology.IsVonNBounded ℝ B)
    (u : Phase) (hu : u ∈ unitThreeSphere)
    (hG : ContDiffAt ℝ ∞ (fun x : Phase => (gauge B x)⁻¹ • x) u),
    let G : Phase → Phase := fun x => (gauge B x)⁻¹ • x
    let f : Phase → ℝ := fun x => zNormSq (G x) + wNormSq (G x)
    ∃! R : Phase,
      u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0 ∧
      f u * phaseRadialContact u R = 1 ∧
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        fderiv ℝ (fun x => f x * phaseRadialContact x w) u R -
          fderiv ℝ (fun x => f x * phaseRadialContact x R) u w = 0) := by sorry
