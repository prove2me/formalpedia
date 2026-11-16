-- Prove2me | Theorems.Thm_APFPaper1_RecordOccupant_gaining_either_side_costs_the_same
-- name    : APFPaper1.RecordOccupant.gaining_either_side_costs_the_same
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:20:49.369178+00:00
-- url     : https://prove2.me/theorems/916b81d1-972e-41eb-8b7e-feb75007b3f3
-- title:
--   Fresh equal-price side records give equal enlarged-set costs
-- statement:
--   If neither rt nor rf is already in K and the two record costs are equal, the sums of costs over insert(rt,K) and insert(rf,K) are equal. No minimization or global uniqueness conclusion is established.
--
--   Publication scope: Exact side-record meanings, fresh records and equal record costs remain the respective hypotheses. Equal extended-record costs do not establish global minimization, a nonunique global minimum, a physical side selector or Born probabilities. The corrected header now states this limit.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper1_RecordOccupant_gaining_a_side.lean:67 (source SHA256 aa9f270a9a6858ec1c6435cbbd6508085663dca60fb64f6bfaa1dafc10d0eeae; APFPaper1.RecordOccupant.gaining_either_side_costs_the_same)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper1_RecordOccupant_gaining_a_side].declarations[APFPaper1.RecordOccupant.gaining_either_side_costs_the_same])', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/publication_comment_corrections/CORRECTIONS.json (SHA256 6f0ad9258c91474be90ee49115bd4c4d303f0759a01bbf3b7e7f7c4c3ac4f777; comment-only correction Theorems.Thm_APFPaper1_RecordOccupant_gaining_a_side)']

import Definitions.Def_APFPaper1_RecordOccupant
import Mathlib.Data.Finset.Insert
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

set_option autoImplicit false
namespace APFPaper1.RecordOccupant
end APFPaper1.RecordOccupant
open APFPaper1.RecordOccupant
variable {X D Rec : Type*}

theorem APFPaper1.RecordOccupant.gaining_either_side_costs_the_same [DecidableEq Rec] (K : Finset Rec) (rt rf : Rec)
    (hrt : rt ∉ K) (hrf : rf ∉ K) (cost : Rec → ℝ) (hc : cost rt = cost rf) :
    ∑ r ∈ insert rt K, cost r = ∑ r ∈ insert rf K, cost r := by sorry
