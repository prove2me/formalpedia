-- Prove2me | solution 1 for moebius_summatory_rpow_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T22:42:18.234431+00:00
-- url     : https://prove2.me/submissions/e33e5777-949b-4faa-b143-5a1b57baf83a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_moebius_dirichlet_partialSum_tendsto_of_half_lt
import Theorems.Thm_ordered_dirichlet_convergence_implies_little_o_partial_sums

theorem solution :
    ∀ ε : ℝ, 0 < ε →
      Asymptotics.IsBigO Filter.atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε)) := by
  intro ε hε
  let σ : ℝ := 1 / 2 + ε
  have hσ : 1 / 2 < σ := by dsimp [σ]; linarith
  obtain ⟨L, hL⟩ := moebius_dirichlet_partialSum_tendsto_of_half_lt σ hσ
  apply (ordered_dirichlet_convergence_implies_little_o_partial_sums
    (fun n => (ArithmeticFunction.moebius n : ℂ)) (σ := σ) (by linarith)
    (L := (L : ℂ)) ?_).isBigO
  have hterm (n : ℕ) :
      (((ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ) =
        (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ (σ : ℂ) := by
    rw [Real.rpow_neg (Nat.cast_nonneg n), Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_cpow (Nat.cast_nonneg n), div_eq_mul_inv]
    push_cast
    rfl
  simpa only [Function.comp_def, Complex.ofReal_sum, hterm] using
    (Complex.continuous_ofReal.tendsto L).comp hL
