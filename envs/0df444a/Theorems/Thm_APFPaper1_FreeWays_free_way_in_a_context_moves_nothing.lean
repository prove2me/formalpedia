-- Prove2me | Theorems.Thm_APFPaper1_FreeWays_free_way_in_a_context_moves_nothing
-- name    : APFPaper1.FreeWays.free_way_in_a_context_moves_nothing
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T04:25:16.720676+00:00
-- url     : https://prove2.me/theorems/15d7dc84-32f1-4cb6-99b2-87092d92bbfc
-- title:
--   free way in a context moves nothing
-- statement:
--   Result: free way in a context moves nothing. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem free_way_in_a_context_moves_nothing (hF : Floor Conn eps) {g : Ctx} {a b : Al g}
--       (h : Conn ⟨g, a⟩ ⟨g, b⟩ 0) : a = b
--   ```
--
--   Module context and limits: Identity, unconditional cross-context Concat and a positive Floor on distinct alignments are explicit hypotheses. Under them free chains returning to a context fix its alignment, and reversible free reach is a renaming. Concat is stronger than the paper's conditional admissible-composition clause; these laws are not adopted inputs or assertions of physical connectivity.
--
--   Source scope parameters:
--
--   ```lean
--   universe u v
--   variable {Ctx : Type u} {Al : Ctx → Type v}
--   variable {Conn : Place Al → Place Al → ℝ → Prop} {eps : Ctx → ℝ}
--   variable {Ctx : Type u} {Al : Ctx → Type v}
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper1_free_ways_under_the_per_realignment_floor:136; pullbacks v46; source SHA-256 529f30c5a3bf2cde9840cd61eb28752149341bafeb1b37a568e95251a8592976']

import Definitions.Def_APFPaper1_free_ways_under_the_per_realignment_floor_Vocabulary
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
set_option autoImplicit false
universe apfNative_u apfNative_v

theorem APFPaper1.FreeWays.free_way_in_a_context_moves_nothing :
∀ {Ctx : Type apfNative_u} {Al : Ctx → Type apfNative_v}
  {Conn :
    @APFPaper1.FreeWays.Place.{apfNative_u, apfNative_v} Ctx Al →
      @APFPaper1.FreeWays.Place.{apfNative_u, apfNative_v} Ctx Al → Real → Prop}
  {eps : Ctx → Real} (hF : @APFPaper1.FreeWays.Floor.{apfNative_u, apfNative_v} Ctx Al Conn eps) {g : Ctx} {a b : Al g}
  (h :
    Conn (@Sigma.mk.{apfNative_u, apfNative_v} Ctx Al g a) (@Sigma.mk.{apfNative_u, apfNative_v} Ctx Al g b)
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))),
  @Eq.{apfNative_v + 1} (Al g) a b := by sorry
