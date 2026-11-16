-- Prove2me | Theorems.Thm_APFPaper5_K1_interface_sharedCost_families
-- name    : APFPaper5.K1.interface_sharedCost_families
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T23:56:59.69608+00:00
-- url     : https://prove2.me/theorems/8b65b9da-5d2d-4917-8a00-1c46c28b13c4
-- title:
--   Exactly served families share the cost of overlapping required supports
-- statement:
--   Under the bridge billing/support hypotheses and exact service of S,T and their union, sharedCost(S,T) equals the sum of costs over the intersection of their required-record unions.
--
--   Publication scope: These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. Expose hbill,hkept,hneed,hS,hT,hST and, for the cardinality identity, hown,hfam,hunit. Shared records in general need not correspond one-to-one to distinctions.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper5_K1_interface_bridge_families.lean:43 (source SHA256 200b53918a2d15d80852011175f1a077a7875950582be7e8a59d473ae4a87797; APFPaper5.K1.interface_sharedCost_families)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper5_K1_interface_bridge_families].declarations[APFPaper5.K1.interface_sharedCost_families])']

import Definitions.Def_APFPaper5_K1_interface_bridge_Vocabulary
import Theorems.Thm_APFPaper5_K1_interface_region_satisfies_K1_of_floor

set_option autoImplicit false

open APFPaper1.Source

namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
variable {D P R Record : Type*} [DecidableEq Record]
  (wholeResource : P → R) (calibration : R → NNReal)
  (maintained : P → Set Record)
  (sufficient : P → Set Record → D → Prop)
  (usesToRealize : P → D → Set Record → Prop)
  (kept : P → Finset Record) (fam : D → Finset Record) (cost : Record → NNReal)

theorem APFPaper5.K1.interface_sharedCost_families [DecidableEq D]
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ∑ r ∈ kept p, (cost r : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S T : Finset D)
    (hS : ExactlyServed maintained sufficient usesToRealize kept fam S)
    (hT : ExactlyServed maintained sufficient usesToRealize kept fam T)
    (hST : ExactlyServed maintained sufficient usesToRealize kept fam (S ∪ T)) :
    sharedCost (familyCost wholeResource calibration maintained sufficient usesToRealize) S T =
      ∑ a ∈ S.biUnion fam ∩ T.biUnion fam, (cost a : ℝ) := by sorry
