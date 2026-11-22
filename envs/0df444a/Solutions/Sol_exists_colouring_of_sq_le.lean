-- Prove2me | solution 1 for exists_colouring_of_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:46:29.192958+00:00
-- url     : https://prove2.me/submissions/487f39cb-8ed1-482d-b6d1-133f96eb6232

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
import Theorems.Thm_exists_of_le
import Theorems.Thm_condition_of_mul_sq
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
theorem _root_.solution {S : Finset G} {k : ℕ} (hk : k ≠ 0) (hm : 3 * k ^ 2 ≤ #S) :
    HasPolychromColouring (Fin k) S := by
-- ANCHOR_END: exists_colouring_of_sq_le
  refine exists_of_le rfl ?_ hk (condition_of_mul_sq hm)
  have : 1 ≤ k := by lia
  grw [← hm, ← this]
  simp
