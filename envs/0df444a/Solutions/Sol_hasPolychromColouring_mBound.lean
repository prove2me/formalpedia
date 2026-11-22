-- Prove2me | solution 1 for hasPolychromColouring_mBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:50:38.180038+00:00
-- url     : https://prove2.me/submissions/7b4f2bab-87f3-41d4-9809-c00fdaef8607

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
import Theorems.Thm_polychromColouringBound_mono
import Theorems.Thm_linear_le_mBound
import Theorems.Thm_polychromColouringBound_mBound

set_option autoImplicit true
open Finset
open Pointwise
variable {G : Type*} [AddCommGroup G]
open MeasureTheory ProbabilityTheory
open Real
open Asymptotics Filter Topology
theorem _root_.solution {S : Finset G} {k : ℕ} (hk : 4 ≤ k) (hS : mBound k ≤ #S) :
    HasPolychromColouring (Fin k) S := by
  have h2S : 2 ≤ #S := by
    grw [← hS, ← linear_le_mBound, ← hk]
    norm_num
  apply exists_of_le rfl (mod_cast h2S) (by grind)
  apply polychromColouringBound_mono (by lia) _ hS (polychromColouringBound_mBound hk)
  · linear_combination linear_le_mBound (k := k)
