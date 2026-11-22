-- Prove2me | solution 1 for exists_colouring_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:53:12.822749+00:00
-- url     : https://prove2.me/submissions/e7a729b1-ab7e-4cd7-8028-e1bf64f241a2

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
import Theorems.Thm_mBound_isLittleO
import Theorems.Thm_hasPolychromColouring_mBound

set_option autoImplicit true
open Finset
open Pointwise
variable {G : Type*} [AddCommGroup G]
open MeasureTheory ProbabilityTheory
open Real
open Asymptotics Filter Topology
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ S : Finset G, (3 + ε) * k * log k ≤ #S →
      HasPolychromColouring (Fin k) S := by
  obtain ⟨f, hf₁, hf₂⟩ := mBound_isLittleO
  rw [isLittleO_one_iff] at hf₁
  filter_upwards [hf₁.eventually_le_const hε, eventually_ge_atTop 4] with k hk hk4 S hS
  apply hasPolychromColouring_mBound hk4
  rify
  grw [hf₂ k (by lia), hk, hS]
