-- Prove2me | Theorems.Thm_Csg_NCSG_combine_compl
-- name    : Csg.NCSG.combine_compl
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:26:18.998428+00:00
-- url     : https://prove2.me/theorems/c3d71d19-b08f-4987-a269-4f18910e51a1
-- title:
--   NCSG: combine compl
-- statement:
--   `combine`, run on `C` and on its complement, rebuilds the exact same joint action either way --
--       the case split is on the same fact (`i ∈ C` versus `i ∈ Cᶜ`) either way, `Finset.mem_compl`
--       deciding one `dite`'s condition from the other's in each branch, closing by the same
--       proof-irrelevance `rfl` `complCoalitionEquiv` itself relies on.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CoalitionComplement.lean#L96-L103
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CoalitionComplement.lean#L96-L103

import Definitions.Def_Csg_Coalition
import Definitions.Def_Csg_CoalitionComplement
set_option autoImplicit true
open Csg
open Csg.NCSG
variable {S Players : Type*} {A : Players → Type*}
  [Fintype S] [Fintype Players] [DecidableEq Players]
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
variable (C : Finset Players)
omit [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

theorem Csg.NCSG.combine_compl (y : ComplementAction A C) (x : ComplementAction A Cᶜ) :
    combine Cᶜ y x = combine C (complCoalitionEquiv C x) y := by sorry
