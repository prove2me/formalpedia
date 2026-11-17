-- Prove2me | Theorems.Thm_APFPaper1_FreeWays_free_round_trip_returns
-- name    : APFPaper1.FreeWays.free_round_trip_returns
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T04:25:15.052061+00:00
-- url     : https://prove2.me/theorems/3aea3d47-8d38-483f-9247-a0f669519540
-- title:
--   free round trip returns
-- statement:
--   Result: free round trip returns. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem free_round_trip_returns (hId : Identity Conn) (hC : Concat Conn) (hF : Floor Conn eps)
--       {g : Ctx} {a b : Al g} {q : Place Al}
--       (h1 : FreeChain Conn ⟨g, a⟩ q) (h2 : FreeChain Conn q ⟨g, b⟩) : a = b
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
--   ['Theorems.Thm_APFPaper1_free_ways_under_the_per_realignment_floor:162; pullbacks v46; source SHA-256 529f30c5a3bf2cde9840cd61eb28752149341bafeb1b37a568e95251a8592976']

import Definitions.Def_APFPaper1_free_ways_under_the_per_realignment_floor_Vocabulary
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
set_option autoImplicit false
universe apfNative_u apfNative_v

theorem APFPaper1.FreeWays.free_round_trip_returns :
∀ {Ctx : Type apfNative_u} {Al : Ctx → Type apfNative_v}
  {Conn :
    @APFPaper1.FreeWays.Place.{apfNative_u, apfNative_v} Ctx Al →
      @APFPaper1.FreeWays.Place.{apfNative_u, apfNative_v} Ctx Al → Real → Prop}
  {eps : Ctx → Real} (hId : @APFPaper1.FreeWays.Identity.{apfNative_u, apfNative_v} Ctx Al Conn)
  (hC : @APFPaper1.FreeWays.Concat.{apfNative_u, apfNative_v} Ctx Al Conn)
  (hF : @APFPaper1.FreeWays.Floor.{apfNative_u, apfNative_v} Ctx Al Conn eps) {g : Ctx} {a b : Al g}
  {q : @APFPaper1.FreeWays.Place.{apfNative_u, apfNative_v} Ctx Al}
  (h1 :
    @APFPaper1.FreeWays.FreeChain.{apfNative_u, apfNative_v} Ctx Al Conn
      (@Sigma.mk.{apfNative_u, apfNative_v} Ctx Al g a) q)
  (h2 :
    @APFPaper1.FreeWays.FreeChain.{apfNative_u, apfNative_v} Ctx Al Conn q
      (@Sigma.mk.{apfNative_u, apfNative_v} Ctx Al g b)),
  @Eq.{apfNative_v + 1} (Al g) a b := by sorry
