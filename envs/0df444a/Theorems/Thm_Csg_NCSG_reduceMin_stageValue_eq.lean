-- Prove2me | Theorems.Thm_Csg_NCSG_reduceMin_stageValue_eq
-- name    : Csg.NCSG.reduceMin_stageValue_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:26:14.098682+00:00
-- url     : https://prove2.me/theorems/2ee3c9d0-258c-420d-9481-b15c8d32f5f0
-- title:
--   NCSG: reduce Min stage Value eq
-- statement:
--   **The one real step.** `⟨⟨Cᶜ⟩⟩P_max`'s stage game at `s` against continuation `v` is literally
--       `⟨⟨C⟩⟩P_min`'s own stage game, rows relabelled by `complCoalitionEquiv C` -- `combine_compl`
--       lifted through `G.K`/`G.r`. `MatrixGameCongr.value_relabelRow` then reads the two stage
--       *values* off as equal, not just the payoff matrices.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CoalitionComplement.lean#L121-L135
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CoalitionComplement.lean#L121-L135

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

theorem Csg.NCSG.reduceMin_stageValue_eq (s : S) (v : S → ℝ) :
    (G.reduceMax Cᶜ).stageValue s v = (G.reduceMin C).stageValue s v := by sorry
