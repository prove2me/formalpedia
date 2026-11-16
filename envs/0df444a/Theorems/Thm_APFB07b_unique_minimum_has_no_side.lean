-- Prove2me | Theorems.Thm_APFB07b_unique_minimum_has_no_side
-- name    : APFB07b.unique_minimum_has_no_side
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T20:09:36.443082+00:00
-- url     : https://prove2.me/theorems/a2bbd5ab-b67a-4e1a-99f7-169199c636f1
-- title:
--   A cost-preserving Boolean-flipping symmetry excludes a unique minimum
-- statement:
--   If sigma preserves admissibility and cost and flips a Boolean reading on every configuration, there is no unique admissible cost minimum. This is an incompatibility result, not construction of a side-less configuration.
--
--   Publication scope: Expose hadm, hcost, hmove/hflip, fixed adm, continuity, finite Configuration and PreconnectedSpace exactly where used. B07a/B07b wrappers consume their declared forms; A2 source fidelity is not newly certified. Infinite is not continuum; the contradiction does not construct a side-less occupant.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFB07b_unique_minimum_symmetry_and_variation.lean:76 (source SHA256 adf52b438bdaaa3d1639c93dd12ea342c0c189ab1e3ef403254b80debf4d395e; APFB07b.unique_minimum_has_no_side)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFB07b_unique_minimum_symmetry_and_variation].declarations[APFB07b.unique_minimum_has_no_side])']

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

theorem APFB07b.unique_minimum_has_no_side (adm : Configuration → Prop) (cost : Configuration → ℝ)
    (sigma : Configuration → Configuration)
    (hadm : ∀ G, adm G → adm (sigma G)) (hcost : ∀ G, cost (sigma G) = cost G)
    (d : Configuration → Bool) (hflip : ∀ G, d (sigma G) = !d G) :
    ¬ ∃ G, IsMinimum adm cost G ∧ ∀ H, IsMinimum adm cost H → H = G := by sorry
