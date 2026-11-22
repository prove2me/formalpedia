-- Prove2me | solution 1 for mBound_isLittleO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:47:52.388642+00:00
-- url     : https://prove2.me/submissions/1080a18e-7ed6-455d-9e94-81044e8bcb66

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
import Theorems.Thm_mBound_zero
import Theorems.Thm_mBound_one
import Theorems.Thm_mBound_pos
import Theorems.Thm_mBound_ne_zero
import Theorems.Thm_mBound_le_helper
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ


attribute [local simp] mBound_zero
attribute [local simp] mBound_one
attribute [local simp] mBound_pos
attribute [local simp] mBound_ne_zero

set_option autoImplicit true
open Finset
open Pointwise
variable {G : Type*} [AddCommGroup G]
open MeasureTheory ProbabilityTheory
open Real
open Asymptotics Filter Topology
theorem _root_.solution :
    ∃ f : ℕ → ℝ, f =o[atTop] (fun _ ↦ 1 : ℕ → ℝ) ∧ ∀ k ≥ 2, mBound k ≤ (3 + f k) * k * log k := by
  refine ⟨fun k ↦ (2 * log (log k) + 6.2) / log k, ?_, ?_⟩
  · rw [isLittleO_one_iff]
    suffices Tendsto (fun x : ℝ ↦ (2 * log x + 6.2) / x) atTop (𝓝 0) from
      this.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have : Tendsto (fun x ↦ log x / x) atTop (𝓝 0) := by
      simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 (by simp)
    simp only [add_div, mul_div_assoc, div_eq_mul_inv (6.2 : ℝ)]
    simpa using (this.const_mul 2).add (tendsto_inv_atTop_zero.const_mul 6.2)
  intro k hk
  have hk' : 0 < log k := log_pos (by simp; lia)
  calc
    (mBound k : ℝ) ≤ k * (3 * log k + (2 * log (log k) + 6.2)) := mBound_le_helper
    _ = (3 + (2 * log (log k) + 6.2) / log k) * k * log k := by simp [field]
