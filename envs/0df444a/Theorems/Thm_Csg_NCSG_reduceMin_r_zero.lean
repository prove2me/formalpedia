-- Prove2me | Theorems.Thm_Csg_NCSG_reduceMin_r_zero
-- name    : Csg.NCSG.reduceMin_r_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:43:21.180578+00:00
-- url     : https://prove2.me/theorems/b2642d70-ff06-428e-bae1-3feb6d7bab54
-- title:
--   NCSG: reduce Min r zero
-- statement:
--   A single `G.r ≡ 0` hypothesis on the underlying `n`-player game gives `reduceMin C`'s own
--       `r ≡ 0` for free -- convenience for callers who'd otherwise have to restate the same fact
--       twice, once per reduction.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CoalitionComplement.lean#L110-L111
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CoalitionComplement.lean#L110-L111

import Definitions.Def_Csg_Coalition
import Definitions.Def_Csg_CoalitionComplement
set_option autoImplicit true
open Csg
open Csg.NCSG
variable {S Players : Type*} {A : Players → Type*}
  [Fintype S] [Fintype Players] [DecidableEq Players]
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
variable (C : Finset Players)
variable (G : NCSG S Players A)

theorem Csg.NCSG.reduceMin_r_zero (hrG : ∀ s a, G.r s a = 0) :
    ∀ s a1 a2, (G.reduceMin C).r s a1 a2 = 0 := by sorry
