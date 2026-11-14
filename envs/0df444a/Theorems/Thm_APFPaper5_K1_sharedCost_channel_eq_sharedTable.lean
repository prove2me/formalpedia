-- Prove2me | Theorems.Thm_APFPaper5_K1_sharedCost_channel_eq_sharedTable
-- name    : APFPaper5.K1.sharedCost_channel_eq_sharedTable
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:54:57.218665+00:00
-- url     : https://prove2.me/theorems/6b0eb037-7f93-42fb-8896-ef32db00988a
-- title:
--   No-new-joint channel costs give a scaled shared-count table
-- statement:
--   Supply a finite channel type, a channel assignment Ch to finite families, a list of indexed families F(a), and a real scale ε. Assume hJ: Ch(F(a)∪F(b))=Ch(F(a))∪Ch(F(b)) for every indexed pair. For cost(X)=ε|Ch(X)|, sharedCost(F(a),F(b)) equals ε times the sharedTable of their channel sets. No positivity of ε is required for the identity. The hypothesis rules out new joint channels for the listed pairs; it is not derived for arbitrary physical joins.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_shared_cost_counting.lean:77; Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex, 1772-1792;2502-2530; Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_two_adoptions_2026-11-12.md, 1

import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APFPaper5_K1_SharedCost
import Theorems.Thm_APFPaper5_K1_sharedTable_eq_card
import Theorems.Thm_APFPaper5_K1_sharedCost_self
import Theorems.Thm_APFPaper5_K1_sharedCost_le_right
import Theorems.Thm_APFPaper5_K1_sharedCost_le_left
import Theorems.Thm_APFPaper5_K1_sharedCost_nonneg_iff
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_ledger
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_no_joint
import Theorems.Thm_APFPaper5_K1_cost_is_count_times_floor
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open APFPaper1.Source
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
universe u v w
variable {ι : Type u} {Rec : Type v} [DecidableEq Rec]

theorem APFPaper5.K1.sharedCost_channel_eq_sharedTable {D : Type u} [DecidableEq D] {Ch : Type v} [Fintype Ch]
    [DecidableEq Ch] {κ : Type w} (chan : Finset D → Finset Ch) (eps : ℝ) (fams : κ → Finset D)
    (hJ : ∀ a b, chan (fams a ∪ fams b) = chan (fams a) ∪ chan (fams b)) (a b : κ) :
    sharedCost (fun X => eps * ((chan X).card : ℝ)) (fams a) (fams b) =
      eps * sharedTable (fun k => chan (fams k)) a b := by sorry
