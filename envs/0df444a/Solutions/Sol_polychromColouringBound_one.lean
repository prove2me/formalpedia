-- Prove2me | solution 1 for polychromColouringBound_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:43:10.464031+00:00
-- url     : https://prove2.me/submissions/cf2efc60-3459-4bf7-b710-a18017c13fa3

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
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ



set_option autoImplicit true
open Finset
open Pointwise
variable {G : Type*} [AddCommGroup G]
open MeasureTheory ProbabilityTheory
open Real
theorem _root_.solution {m : ℕ} (hm : m ≠ 0) : polychromColouringBound 1 m := by
  simp [polychromColouringBound, hm]
