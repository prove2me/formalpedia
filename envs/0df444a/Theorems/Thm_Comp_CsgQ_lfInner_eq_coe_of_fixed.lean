-- Prove2me | Theorems.Thm_Comp_CsgQ_lfInner_eq_coe_of_fixed
-- name    : Comp.CsgQ.lfInner_eq_coe_of_fixed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:02:49.272795+00:00
-- url     : https://prove2.me/theorems/2c357ae2-194c-49c5-aa98-10348a6260c9
-- title:
--   Csg Q: lf Inner eq coe of fixed
-- statement:
--   **The middle payoff.** A region the middle chain reached and that the middle step leaves fixed
--       *is* the `μX` fixed point at `y`, exactly. That is one `νY`-step's worth of computation,
--       certified.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitReach.lean#L114-L121
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitReach.lean#L114-L121

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeLimitReach
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.lfInner_eq_coe_of_fixed (G : CsgQ S A1 A2) (h : G.WellFormed) (b y c : Finset S)
    (w : S → Finset A1) (hw : ∀ s, (G.toCSG h).LW ↑c ↑y s = (↑(w s) : Set A1))
    (hfix : c = G.lpre1F w c ∪ b)
    (hle : (↑c : Set S) ≤ ((G.toCSG h).LFInner ↑b ↑y).lfp) :
    ((G.toCSG h).LFInner ↑b ↑y).lfp = (↑c : Set S) := by sorry
