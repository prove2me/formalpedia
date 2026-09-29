-- Prove2me | solution 1 for ns_lemma2_nonneg
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-09T03:14:38.878834+00:00
-- url     : https://prove2.me/submissions/a74a903f-773e-41b5-9d17-83af91fb3d65
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ns_markov_grid_lemma
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic

open Polynomial Set

/-- Sketch: reduce NS 1994 Lemma 2 (nonnegative form) to the Markov-on-the-grid
derivative bound `ns_markov_grid_lemma`.

Argument: if `b ≤ 2d²` we are done; otherwise `d² < b`. By MVT on `[0,1]`, using
`Q(0) = 0` and `Q(1) = 1`, there is `ξ ∈ (0,1)` with `Q'(ξ) = 1`. The child
lemma (a Markov / Coppersmith–Rivlin style bound) gives `|Q'(ξ)| ≤ d²/(b-d²)`.
Hence `1 ≤ d²/(b-d²)`, so `b - d² ≤ d²`, so `b ≤ 2d²` — contradiction. -/
theorem solution : ∀ {b : ℕ} (hb : 1 ≤ b) (Q : Polynomial ℝ) {d : ℕ} (h_deg : Q.natDegree ≤ d) (h_zero : Q.eval 0 = 0) (h_one : Q.eval 1 = 1) (h_lo : ∀ t : ℕ, t ≤ b → 0 ≤ Q.eval (t : ℝ)) (h_hi : ∀ t : ℕ, t ≤ b → Q.eval (t : ℝ) ≤ 1), b ≤ 2 * d^2 := by
  intro b hb Q d h_deg h_zero h_one h_lo h_hi
  by_cases hdb : b ≤ 2 * d ^ 2
  · exact hdb
  exfalso
  push_neg at hdb
  -- `hdb : 2 * d^2 < b`.
  have hd2b : (d : ℝ) ^ 2 < (b : ℝ) := by
    have : (2 : ℝ) * (d : ℝ) ^ 2 < (b : ℝ) := by exact_mod_cast hdb
    nlinarith [sq_nonneg (d : ℝ)]
  -- MVT on `[0,1]`: `∃ ξ ∈ (0,1), Q'(ξ) = 1`.
  obtain ⟨ξ, hξmem, hξ⟩ := exists_hasDerivAt_eq_slope
    (fun x => Q.eval x) (fun x => Q.derivative.eval x)
    (show (0 : ℝ) < 1 by norm_num)
    ((Polynomial.continuous Q).continuousOn)
    (fun x _ => Polynomial.hasDerivAt Q x)
  rw [h_zero, h_one] at hξ
  norm_num at hξ
  -- `hξ : Q.derivative.eval ξ = 1`; `hξmem : ξ ∈ Ioo 0 1`.
  have hξ0 : (0 : ℝ) ≤ ξ := le_of_lt hξmem.1
  have hξb : ξ ≤ (b : ℝ) := by
    have : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith [hξmem.2]
  -- Apply the Markov child.
  have hmarkov := ns_markov_grid_lemma hb Q h_deg h_lo h_hi hd2b ξ hξ0 hξb
  rw [hξ] at hmarkov
  have h1 : (1 : ℝ) ≤ (d : ℝ) ^ 2 / ((b : ℝ) - (d : ℝ) ^ 2) := (le_abs_self 1).trans hmarkov
  have hbd2 : (0 : ℝ) < (b : ℝ) - (d : ℝ) ^ 2 := by linarith
  have h2 : (b : ℝ) - (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right h1 (le_of_lt hbd2)
    rw [one_mul, div_mul_cancel₀ _ (ne_of_gt hbd2)] at hm
    exact hm
  have hble : (b : ℝ) ≤ 2 * (d : ℝ) ^ 2 := by linarith
  have hnat : b ≤ 2 * d ^ 2 := by exact_mod_cast hble
  omega
