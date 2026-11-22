-- Prove2me | Theorems.Thm_Csg_CSG_exists_forall_le_add_of_tendsto
-- name    : Csg.CSG.exists_forall_le_add_of_tendsto
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:16:49.616599+00:00
-- url     : https://prove2.me/theorems/3220a931-e05a-48f5-bf31-41df75eda8e7
-- title:
--   CSG: exists forall le add of tendsto
-- statement:
--   Finite-index "monotone convergence is eventually uniform": if `d n s'` tends to `g s'` for
--       every `s'` ranging over a `Fintype`, there is a single `N` past which `d n` is within any given
--       `δ` of `g` at *every* state at once, not just eventually at each state separately.
--       `Filter.eventually_all` is exactly the fact that lets finitely many individual `∀ᶠ` statements
--       swap into one `∀ᶠ` of the conjunction. It needs only `Finite S`, not `Fintype S`'s enumeration
--       data, so this is the one declaration in the file taking `[Finite S]` while omitting the ambient
--       `[Fintype S]`; callers are unaffected, since `Fintype` yields `Finite` by instance.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ReachConverge.lean#L97-L103
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ReachConverge.lean#L97-L103

import Definitions.Def_Csg_ReachOp
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Order.FixedPoints
import Mathlib.Order.OmegaCompletePartialOrder
import Definitions.Def_Csg_ReachConverge
set_option autoImplicit true
open Csg
open Csg.CSG
open OmegaCompletePartialOrder Filter Topology
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
omit [Fintype S]

theorem Csg.CSG.exists_forall_le_add_of_tendsto [Finite S] {g : S → ℝ} {d : ℕ → S → ℝ}
    (htendsto : ∀ s', Tendsto (fun n => d n s') atTop (𝓝 (g s'))) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N, ∀ n ≥ N, ∀ s', g s' ≤ d n s' + δ := by sorry
