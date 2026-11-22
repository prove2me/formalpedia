-- Prove2me | solution 1 for le_polychromNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:40:40.765787+00:00
-- url     : https://prove2.me/submissions/6e276c3c-91b0-44c3-8c25-a6191e3af159

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber

set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
theorem _root_.solution {n : ℕ} (hn : HasPolychromColouring (Fin n) S) :
    n ≤ polychromNumber S :=
  le_csSup bddAbove hn
