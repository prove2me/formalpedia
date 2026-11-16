-- Prove2me | Theorems.Thm_APFPaper5_K1_counted_family_satisfies_K1_of_nonneg_shared
-- name    : APFPaper5.K1.counted_family_satisfies_K1_of_nonneg_shared
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T23:29:13.317611+00:00
-- url     : https://prove2.me/theorems/e3b465d4-ffe2-49f3-be9d-75580027fe45
-- title:
--   Nonnegative higher-order book weights complete the counted-family table implication
-- statement:
--   For an admissible tested finite family novel member-by-member over the complements, guarded B05 and nonnegative book weights for every subset of size at least two imply a bilinear shared-cost table with faithful nonnegative diagonal under identity exchange.
--
--   Publication scope: These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. hshared is NOT ADOPTED or derived. It requires nonnegative higher-order Mobius/book weights, not merely pairwise nonnegative shared costs. Expose hregion,htested,hnov and exact B05 guards. Pass30/31 are outside this batch and do not refute the fully conditioned theorem; the pass30 residue example did not check the counted-family premises.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper5_K1_interface_cost_book.lean:90 (source SHA256 58ee305ebea34f8a0fe99e90449a861888366cfe12adc3e63deafd414f99ff06; APFPaper5.K1.counted_family_satisfies_K1_of_nonneg_shared)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper5_K1_interface_cost_book].declarations[APFPaper5.K1.counted_family_satisfies_K1_of_nonneg_shared])']

import Definitions.Def_APFPaper5_K1_interface_cost_book_Vocabulary
import Definitions.Def_APFPaper5_K1_cost_book_Vocabulary
import Theorems.Thm_APFPaper5_K1_book_empty
import Theorems.Thm_APFPaper5_K1_book_singleton
import Theorems.Thm_APFPaper5_K1_cost_table_satisfies_K1
import Theorems.Thm_APFB05_overfull_chain_not_admissible
import Theorems.Thm_APFB05_no_admissible_family_contains_overfull_chain
import Theorems.Thm_APFB05_no_room_for_new_record
import Theorems.Thm_APFPaper1_Source_familyCost_nonneg
import Theorems.Thm_APFPaper1_Source_familyCost_mono
import Definitions.Def_APF_B05_DeclaredInput_r2

set_option autoImplicit false

open APFPaper1.Source

namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5
open APFPaper5.K1
variable {D P R Record : Type*} [DecidableEq D] {ι : Type} [Fintype ι] [DecidableEq ι]
  (wholeResource : P → R) (calibration : R → NNReal)
  (maintained : P → Set Record)
  (sufficient : P → Set Record → D → Prop)
  (usesToRealize : P → D → Set Record → Prop)

theorem APFPaper5.K1.counted_family_satisfies_K1_of_nonneg_shared (tested : D → Prop) (C eps : ℝ)
    (hB05 : APFB05.MarginalFloor (Context := Unit) (D := fun _ => D) (P := fun _ => P)
      (R := fun _ => R) (Record := fun _ => Record) (fun _ => wholeResource) (fun _ => calibration)
      (fun _ => maintained) (fun _ => sufficient) (fun _ => usesToRealize) (fun _ => tested)
      (fun _ => C) (fun _ => eps))
    (dist : ι → D)
    (hregion : familyAdmissible wholeResource calibration maintained sufficient usesToRealize C
      (Finset.univ.image dist))
    (htested : ∀ i, tested (dist i))
    (hnov : ∀ i, supportNovel wholeResource calibration maintained sufficient usesToRealize
      ((({i} : Finset ι)ᶜ).image dist) (dist i))
    (hshared : ∀ T : Finset ι, 2 ≤ T.card →
      0 ≤ book (indexedCost wholeResource calibration maintained sufficient usesToRealize dist) T) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ)
        (tableForm (fun i j : ι => sharedCost
          (indexedCost wholeResource calibration maintained sufficient usesToRealize dist)
          {i} {j})) ∧
      FaithfulNonnegDiagonal
        (tableForm (fun i j : ι => sharedCost
          (indexedCost wholeResource calibration maintained sufficient usesToRealize dist)
          {i} {j}))
        (LinearEquiv.refl ℝ (ι → ℝ)) := by sorry
