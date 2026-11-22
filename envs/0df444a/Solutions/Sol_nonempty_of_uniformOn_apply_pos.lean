-- Prove2me | solution 1 for nonempty_of_uniformOn_apply_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:43:44.529182+00:00
-- url     : https://prove2.me/submissions/2b8fda91-a771-4c6b-9716-99222b62a200

import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.NNRat.Floor
import Mathlib.Tactic.Rify
import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_Compactness
import Definitions.Def_Polychromatic_LocalLemma
import Definitions.Def_Polychromatic_Existence
import Theorems.Thm_P2M_nonempty_of_uniformOn_apply_pos__06fe7251a306

set_option autoImplicit true
open Finset
open Pointwise
variable {G : Type*} [AddCommGroup G]
open MeasureTheory ProbabilityTheory
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] {s t : Set Ω} (h : 0 < uniformOn s t) :
    (s ∩ t).Nonempty := by
  have hs_fin : s.Finite := finite_of_uniformOn_ne_zero h.ne'
  exact nonempty_of_uniformOn_apply_pos' h (hs_fin.measurableSet)
