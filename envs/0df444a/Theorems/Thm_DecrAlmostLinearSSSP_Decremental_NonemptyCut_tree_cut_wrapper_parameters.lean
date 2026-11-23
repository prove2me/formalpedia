-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_NonemptyCut_tree_cut_wrapper_parameters
-- name    : DecrAlmostLinearSSSP.Decremental.NonemptyCut.tree_cut_wrapper_parameters
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:46:18.126698+00:00
-- url     : https://prove2.me/theorems/469d1377-285c-49dd-a0d1-7a369cb4b3fc
-- title:
--   Subpolynomial parameters and work envelope for the tree-cut wrapper
-- statement:
--   For the normalized tree-cut parameters $K_0,h_0,a_0,C_0$, define
--   \[
--   K=\max\{32,K_0\},\quad h=64(1+h_0),\quad \Gamma=1,\quad
--    a=16(1+a_0),\quad C=C_0+16.
--   \]
--   These functions retain the required subpolynomial and approximation-quality bounds. Moreover, if a complete public trace has $q$ public operations, $R+q$ detector reports, and private-plus-wrapper work
--   \[
--   W\le 7\bigl(C_0ma_0(m)+h_0(m)(2q+2R)\bigr)+32m+40(q+R),
--   \]
--   then the public charged total, including $6q$ front-end steps, is at most $Cma(m)+h(m)(q+R)$. This is the explicit scalar-RAM overhead accounting used to implement Lemma 3.2 from the normalized tree protocol.
-- source:
--   Source #912, Lemma 3.2, p.9 (public dynamic-cut work bound); formal companion accounting for the charged tree-cut wrapper.

import Definitions.Def_DecrAlmostLinearSSSP_TreeCutProtocol

set_option autoImplicit false
open scoped ENNReal NNReal

/-- Explicit subpolynomial parameters and the arithmetic envelope used by the charged
public wrapper. The initialization and operation allowances absorb seven-fold guest
simulation, linear input transformation and constant work per public or private call. -/
theorem DecrAlmostLinearSSSP.Decremental.NonemptyCut.tree_cut_wrapper_parameters
    (K₀ h₀ a₀ : ℕ → ℝ) (C₀ : ℝ)
    (hC₀ : 0 < C₀) (hK₀ : Subpolynomial K₀) (hh₀ : Subpolynomial h₀)
    (ha₀ : Subpolynomial a₀)
    (hquality : ∀ m, K₀ m ≤ Real.rpow 2
      (C₀ * Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) *
        max 1 (Real.log (Real.log (max 2 m : ℕ))))) :
    ∃ (K h Γ a : ℕ → ℝ) (C : ℝ),
      0 < C ∧ Subpolynomial K ∧ Subpolynomial h ∧ Subpolynomial Γ ∧ Subpolynomial a ∧
      (∀ m, 32 ≤ K m ∧ K m ≤ Real.rpow 2
        (C * Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) *
          max 1 (Real.log (Real.log (max 2 m : ℕ))))) ∧
      K = (fun m => max 32 (K₀ m)) ∧ h = (fun m => 64 * (1 + h₀ m)) ∧
      Γ = (fun _ => 1) ∧ a = (fun m => 16 * (1 + a₀ m)) ∧ C = C₀ + 16 ∧
      ∀ (m : ℕ) (q R W : ℝ), 0 ≤ q → 0 ≤ R → 0 ≤ W →
        W ≤ 7 * (C₀ * m * a₀ m + h₀ m * (2 * q + 2 * R)) + 32 * m + 40 * (q + R) →
        W + 6 * q ≤ C * m * a m + h m * (q + R) := by sorry
