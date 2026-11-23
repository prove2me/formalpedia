-- Prove2me | Theorems.Thm_Csg_CSG_coBuchiInnerOpFun_coe
-- name    : Csg.CSG.coBuchiInnerOpFun_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:13:15.359852+00:00
-- url     : https://prove2.me/theorems/95da3f32-9ce3-4863-ad5e-af02cb5ed01f
-- title:
--   CSG: co Buchi Inner Op Fun coe
-- statement:
--   **The payoff.** The coercion of `coBuchiInnerOpFun` to `ℝ`, as a plain `if`-`then`-`else` with
--       no subtype packaging left to get in the way. Consumers that need to reason about the *value* of
--       `coBuchiInnerOpFun` -- rather than just its monotonicity -- should rewrite with this first:
--       `coBuchiInnerOpFun`'s own definition packages each branch as an anonymous-constructor element
--       of `Set.Icc (0 : ℝ) 1` (value plus a two-part membership proof), and Mathlib's `rw`/`show`
--       machinery can fail to see through that packaging at the transparency level those tactics check
--       against -- concretely, `rw [if_pos h]`/`rw [if_neg h]` applied directly to an
--       unfolded
--       `coBuchiInnerOpFun` goal can report a spurious "motive is not type correct" or pattern-matching
--       failure, even though the two sides are definitionally equal. Working with this `ℝ`-valued
--       equation instead avoids the packaging entirely: `split_ifs` produces two goals, each closed by
--       `rfl` since `(⟨v, _⟩ : Set.Icc _ _)`'s coercion to `ℝ` is its first component by definition.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CoBuchiOp.lean#L79-L84
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CoBuchiOp.lean#L79-L84

import Definitions.Def_Csg_BuchiOp
import Definitions.Def_Csg_CoBuchiOp
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.coBuchiInnerOpFun_coe (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (x y : S → Set.Icc (0 : ℝ) 1) (s : S) :
    (C.coBuchiInnerOpFun U hr x y s : ℝ) = if U s then C.stageValue s (fun s' => (y s' : ℝ))
      else C.stageValue s (fun s' => (x s' : ℝ)) := by sorry
