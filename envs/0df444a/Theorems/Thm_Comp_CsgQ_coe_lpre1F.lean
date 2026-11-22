-- Prove2me | Theorems.Thm_Comp_CsgQ_coe_lpre1F
-- name    : Comp.CsgQ.coe_lpre1F
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:08:27.625097+00:00
-- url     : https://prove2.me/theorems/e197e9ab-90a1-4129-b3f0-aa7084848ead
-- title:
--   Csg Q: coe lpre1 F
-- statement:
--   `lpre1F` is `CSG.Lpre1`, provided the witness family really is `LW`. `coe_bF` inside, then
--       `Finset.coe_eq_univ` to turn the `Set`-level `= Set.univ` test into the decidable `Finset`
--       one.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitReach.lean#L84-L89
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitReach.lean#L84-L89

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeLimitReach
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.coe_lpre1F (G : CsgQ S A1 A2) (h : G.WellFormed) (w : S → Finset A1) (x y : Finset S)
    (hw : ∀ s, (G.toCSG h).LW ↑x ↑y s = (↑(w s) : Set A1)) :
    (↑(G.lpre1F w x) : Set S) = (G.toCSG h).Lpre1 ↑x ↑y := by sorry
