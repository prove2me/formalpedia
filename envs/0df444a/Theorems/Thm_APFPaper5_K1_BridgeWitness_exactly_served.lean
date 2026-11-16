-- Prove2me | Theorems.Thm_APFPaper5_K1_BridgeWitness_exactly_served
-- name    : APFPaper5.K1.BridgeWitness.exactly_served
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T23:50:07.833122+00:00
-- url     : https://prove2.me/theorems/e19fd2d4-607f-4b0f-b451-666c03b33336
-- title:
--   Shared-plus-private witness: the shared-plus-private book exactly serves every finite family
-- statement:
--   In the shared-plus-private witness, in the supplied witness book where finite record sets are protocols, every finite distinction family has a protocol keeping exactly its support union and serving its members.
--
--   Publication scope: These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. A nonvacuity witness for the conditional bridge, not a world of all eight original forms and not a physical interface. Fintype index is explicit.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper5_K1_interface_bridge_witness.lean:43 (source SHA256 06c30dd08392db174f046e2ea867a087c55142867caabf1292f4d6dbde73c544; APFPaper5.K1.BridgeWitness.exactly_served)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper5_K1_interface_bridge_witness].declarations[APFPaper5.K1.BridgeWitness.exactly_served])']

import Definitions.Def_APFPaper5_K1_interface_bridge_witness_Vocabulary
import Definitions.Def_APFPaper5_K1_interface_bridge_Vocabulary
import Theorems.Thm_APFPaper5_K1_interface_region_satisfies_K1_of_floor
import Theorems.Thm_APFPaper5_K1_weighted_marginal_ge
import Theorems.Thm_APFB05_weighted_record_model_satisfies_floor
import Theorems.Thm_APFPaper5_K1_needs_own_record_of_separates
import Theorems.Thm_APFPaper5_K1_recordModel_supportNovel_of_needs_own_record
import Theorems.Thm_APFPaper5_K1_recordModel_economy_of_separation

set_option autoImplicit false

open APFPaper1.Source

namespace APFPaper5.K1.BridgeWitness
end APFPaper5.K1.BridgeWitness
open APFPaper5
open APFPaper5.K1
open APFPaper5.K1.BridgeWitness
variable {ι : Type} [DecidableEq ι]

theorem APFPaper5.K1.BridgeWitness.exactly_served (S : Finset ι) :
    ExactlyServed (fun p : Finset (Option ι) => (↑p : Set (Option ι)))
      (fun _ sigma d => (↑(fam d) : Set (Option ι)) ⊆ sigma) (fun _ _ _ => True)
      (fun p : Finset (Option ι) => p) fam S := by sorry
