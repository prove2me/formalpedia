-- Prove2me | Theorems.Thm_APFPaper5_K1_interface_region_satisfies_K1_of_floor
-- name    : APFPaper5.K1.interface_region_satisfies_K1_of_floor
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T23:35:19.049214+00:00
-- url     : https://prove2.me/theorems/18e0bf55-a993-4070-ae83-9ce520f81d2f
-- title:
--   Guarded B05 plus scoped exact service gives the finite table result
-- statement:
--   For finite indices and records, under additive billing/support conditions, guarded B05, exact service of every admissible family, an admissible tested indexed family and novelty of each member over the others, the shared-cost table is bilinear with faithful nonnegative diagonal under identity exchange.
--
--   Publication scope: These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. Keep hbill, hkept, hneed, ExactlyServed, hprivate or the complete B05/hscoped/hregion/htested/hnov alternative. Fintype Record and Fintype index are required for the table conclusions. No original-interface binding is certified merely because parameters carry source names.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper5_K1_interface_bridge.lean:224 (source SHA256 189aab98d30bc7e74e263c3d4896d69bed688e0bef01cf65b0d28362ee12eded; APFPaper5.K1.interface_region_satisfies_K1_of_floor)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper5_K1_interface_bridge].declarations[APFPaper5.K1.interface_region_satisfies_K1_of_floor])']

import Definitions.Def_APFPaper5_K1_interface_bridge_Vocabulary
import Theorems.Thm_APFPaper1_Source_sum_needed_le_bill
import Theorems.Thm_APFPaper1_Source_familyCost_eq_sum_of_available
import Theorems.Thm_APFPaper1_Source_supportNovel_of_private_record
import Theorems.Thm_APFPaper1_Source_supportNovel_of_private_record_count
import Theorems.Thm_APFPaper1_Source_marginal_ge_of_private_record
import Theorems.Thm_APFPaper1_Source_each_private_excludes_riding
import Theorems.Thm_APFPaper1_Source_supportNovel_of_each_private
import Theorems.Thm_APFPaper1_Source_marginal_zero_of_no_own_record
import Theorems.Thm_APFPaper1_Source_needs_own_record_of_supportNovel
import Theorems.Thm_APFPaper5_K1_familyCost_weighted
import Theorems.Thm_APFPaper5_K1_recordModelCost_eq
import Theorems.Thm_APFPaper5_K1_recordModel_sharedCost
import Theorems.Thm_APFPaper5_K1_recordModel_satisfies_K1
import Theorems.Thm_APFB05_overfull_chain_not_admissible
import Theorems.Thm_APFB05_no_admissible_family_contains_overfull_chain
import Theorems.Thm_APFB05_no_room_for_new_record
import Definitions.Def_APF_B05_DeclaredInput_r2

set_option autoImplicit false

open APFPaper1.Source

namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5
open APFPaper5.K1
variable {D P R Record : Type*} [DecidableEq Record]
  (wholeResource : P → R) (calibration : R → NNReal)
  (maintained : P → Set Record)
  (sufficient : P → Set Record → D → Prop)
  (usesToRealize : P → D → Set Record → Prop)
  (kept : P → Finset Record) (fam : D → Finset Record) (cost : Record → NNReal)

theorem APFPaper5.K1.interface_region_satisfies_K1_of_floor {ι : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq D] [Fintype Record]
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ∑ r ∈ kept p, (cost r : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (tested : D → Prop) (C eps : ℝ)
    (hB05 : APFB05.MarginalFloor (Context := Unit) (D := fun _ => D) (P := fun _ => P)
      (R := fun _ => R) (Record := fun _ => Record) (fun _ => wholeResource) (fun _ => calibration)
      (fun _ => maintained) (fun _ => sufficient) (fun _ => usesToRealize) (fun _ => tested)
      (fun _ => C) (fun _ => eps))
    (hscoped : ∀ S : Finset D,
      familyAdmissible wholeResource calibration maintained sufficient usesToRealize C S →
      ExactlyServed maintained sufficient usesToRealize kept fam S)
    (dist : ι → D)
    (hregion : familyAdmissible wholeResource calibration maintained sufficient usesToRealize C
      (Finset.univ.image dist))
    (htested : ∀ i, tested (dist i))
    (hnov : ∀ i, supportNovel wholeResource calibration maintained sufficient usesToRealize
      ((Finset.univ.erase i).image dist) (dist i)) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ)
        (tableForm (fun i j : ι => sharedCost
          (familyCost wholeResource calibration maintained sufficient usesToRealize)
          {dist i} {dist j})) ∧
      FaithfulNonnegDiagonal
        (tableForm (fun i j : ι => sharedCost
          (familyCost wholeResource calibration maintained sufficient usesToRealize)
          {dist i} {dist j}))
        (LinearEquiv.refl ℝ (ι → ℝ)) := by sorry
