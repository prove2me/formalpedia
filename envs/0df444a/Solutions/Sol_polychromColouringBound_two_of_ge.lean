-- Prove2me | solution 1 for polychromColouringBound_two_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:44:38.766502+00:00
-- url     : https://prove2.me/submissions/f805d4ec-3eeb-4361-8e11-2172e2e4c30a

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
import Theorems.Thm_polychromColouringBound_mono

set_option autoImplicit true
open Finset
open Pointwise
variable {G : Type*} [AddCommGroup G]
open MeasureTheory ProbabilityTheory
open Real
theorem _root_.solution {m : ℕ} (hm : 9 ≤ m) : polychromColouringBound 2 m := by
  apply polychromColouringBound_mono (by norm_num) (by norm_num) hm
  grw [polychromColouringBound, Real.exp_one_lt_d9]
  norm_num
