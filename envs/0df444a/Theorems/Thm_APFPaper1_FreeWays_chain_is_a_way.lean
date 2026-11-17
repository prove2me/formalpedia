-- Prove2me | Theorems.Thm_APFPaper1_FreeWays_chain_is_a_way
-- name    : APFPaper1.FreeWays.chain_is_a_way
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T04:23:39.94648+00:00
-- url     : https://prove2.me/theorems/0e44b543-78ca-4f04-859f-289049e2318c
-- title:
--   chain is a way
-- statement:
--   Result: chain is a way. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem chain_is_a_way (hId : Identity Conn) (hC : Concat Conn) {p r : Place Al} {s : ℝ}
--       (h : Chain Conn p r s) : ∃ c, c ≤ s ∧ Conn p r c
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
--   ['Theorems.Thm_APFPaper1_free_ways_under_the_per_realignment_floor:126; pullbacks v46; source SHA-256 529f30c5a3bf2cde9840cd61eb28752149341bafeb1b37a568e95251a8592976']

import Definitions.Def_APFPaper1_free_ways_under_the_per_realignment_floor_Vocabulary
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
set_option autoImplicit false
universe apfNative_u apfNative_v

theorem APFPaper1.FreeWays.chain_is_a_way :
∀ {Ctx : Type apfNative_u} {Al : Ctx → Type apfNative_v}
  {Conn :
    @APFPaper1.FreeWays.Place.{apfNative_u, apfNative_v} Ctx Al →
      @APFPaper1.FreeWays.Place.{apfNative_u, apfNative_v} Ctx Al → Real → Prop}
  (hId : @APFPaper1.FreeWays.Identity.{apfNative_u, apfNative_v} Ctx Al Conn)
  (hC : @APFPaper1.FreeWays.Concat.{apfNative_u, apfNative_v} Ctx Al Conn)
  {p r : @APFPaper1.FreeWays.Place.{apfNative_u, apfNative_v} Ctx Al} {s : Real}
  (h : @APFPaper1.FreeWays.Chain.{apfNative_u, apfNative_v} Ctx Al Conn p r s),
  @Exists.{1} Real fun (c : Real) => And (@LE.le.{0} Real Real.instLE c s) (Conn p r c) := by sorry
