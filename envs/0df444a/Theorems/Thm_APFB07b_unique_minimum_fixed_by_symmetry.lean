-- Prove2me | Theorems.Thm_APFB07b_unique_minimum_fixed_by_symmetry
-- name    : APFB07b.unique_minimum_fixed_by_symmetry
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T20:08:36.57097+00:00
-- url     : https://prove2.me/theorems/d5b81324-fd21-4f8b-824a-4170a35965c4
-- title:
--   An admissibility- and cost-preserving map fixes a unique minimum
-- statement:
--   If sigma preserves admissibility and each configuration's cost, it fixes any admissible minimum that is unique among all minima.
--
--   Publication scope: Expose hadm, hcost, hmove/hflip, fixed adm, continuity, finite Configuration and PreconnectedSpace exactly where used. B07a/B07b wrappers consume their declared forms; A2 source fidelity is not newly certified. Infinite is not continuum; the contradiction does not construct a side-less occupant.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFB07b_unique_minimum_symmetry_and_variation.lean:56 (source SHA256 adf52b438bdaaa3d1639c93dd12ea342c0c189ab1e3ef403254b80debf4d395e; APFB07b.unique_minimum_fixed_by_symmetry)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFB07b_unique_minimum_symmetry_and_variation].declarations[APFB07b.unique_minimum_fixed_by_symmetry])']

import Definitions.Def_APF_B07a_DeclaredInput
import Definitions.Def_APF_B07b_DeclaredInput
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false
namespace APFB07b
end APFB07b
open APFB07b
variable {Configuration : Type*}

theorem APFB07b.unique_minimum_fixed_by_symmetry (adm : Configuration → Prop) (cost : Configuration → ℝ)
    (sigma : Configuration → Configuration)
    (hadm : ∀ G, adm G → adm (sigma G)) (hcost : ∀ G, cost (sigma G) = cost G)
    (G : Configuration) (hmin : IsMinimum adm cost G)
    (huniq : ∀ H, IsMinimum adm cost H → H = G) : sigma G = G := by sorry
