-- Prove2me | Theorems.Thm_APFPaper1_FreeWays_chain_back_to_a_context_costs_the_floor
-- name    : APFPaper1.FreeWays.chain_back_to_a_context_costs_the_floor
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T04:23:38.152782+00:00
-- url     : https://prove2.me/theorems/2e710d87-ee84-4b79-b772-6368509b7caf
-- title:
--   chain back to a context costs the floor
-- statement:
--   Result: chain back to a context costs the floor. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem chain_back_to_a_context_costs_the_floor (hId : Identity Conn) (hC : Concat Conn)
--       (hF : Floor Conn eps) {g : Ctx} {a b : Al g} {s : ℝ}
--       (h : Chain Conn ⟨g, a⟩ ⟨g, b⟩ s) (hne : a ≠ b) : eps g ≤ s
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
--   ['Theorems.Thm_APFPaper1_free_ways_under_the_per_realignment_floor:144; pullbacks v46; source SHA-256 529f30c5a3bf2cde9840cd61eb28752149341bafeb1b37a568e95251a8592976']

import Definitions.Def_APFPaper1_free_ways_under_the_per_realignment_floor_Vocabulary
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
set_option autoImplicit false
universe apfNative_u apfNative_v

theorem APFPaper1.FreeWays.chain_back_to_a_context_costs_the_floor :
∀ {Ctx : Type apfNative_u} {Al : Ctx → Type apfNative_v}
  {Conn :
    @APFPaper1.FreeWays.Place.{apfNative_u, apfNative_v} Ctx Al →
      @APFPaper1.FreeWays.Place.{apfNative_u, apfNative_v} Ctx Al → Real → Prop}
  {eps : Ctx → Real} (hId : @APFPaper1.FreeWays.Identity.{apfNative_u, apfNative_v} Ctx Al Conn)
  (hC : @APFPaper1.FreeWays.Concat.{apfNative_u, apfNative_v} Ctx Al Conn)
  (hF : @APFPaper1.FreeWays.Floor.{apfNative_u, apfNative_v} Ctx Al Conn eps) {g : Ctx} {a b : Al g} {s : Real}
  (h :
    @APFPaper1.FreeWays.Chain.{apfNative_u, apfNative_v} Ctx Al Conn (@Sigma.mk.{apfNative_u, apfNative_v} Ctx Al g a)
      (@Sigma.mk.{apfNative_u, apfNative_v} Ctx Al g b) s)
  (hne : @Ne.{apfNative_v + 1} (Al g) a b), @LE.le.{0} Real Real.instLE (eps g) s := by sorry
