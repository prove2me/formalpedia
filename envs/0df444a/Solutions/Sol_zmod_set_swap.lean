-- Prove2me | solution 1 for zmod_set_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:41:47.888591+00:00
-- url     : https://prove2.me/submissions/5478da77-f01b-476c-af93-7f78e8812322

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Mathlib.Algebra.Ring.AddAut
import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour

set_option autoImplicit true
open Finset Pointwise
theorem _root_.solution (m : ℕ) (a b : ℤ) : zmod_set m (-a) (b - a) = zmod_set m a b := by
  grind [zmod_set]
