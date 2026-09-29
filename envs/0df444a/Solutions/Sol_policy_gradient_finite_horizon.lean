-- Prove2me | solution 1 for policy_gradient_finite_horizon
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-10T04:21:56.669879+00:00
-- url     : https://prove2.me/submissions/e73fefb2-81ff-455b-8f1b-0532980d16b6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_pg_bellman_step
import Definitions.Def_pg_mdp_core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Finset

namespace PGUnroll

variable {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]
variable (P : S → A → S → ℝ) (r : S → A → ℝ) (π : ℝ → S → A → ℝ) (θ : ℝ)

/-- The "score" functional: `Φ k s = ∑_a Q_k(s,a) · π'(s,a)`. -/
noncomputable def Φ (k : ℕ) (s : S) : ℝ :=
  ∑ a : A, pgQ P r π k θ s a * deriv (fun θ' => π θ' s a) θ

/-- The aggregated one-step transition weight from `s₀` to `s'`. -/
noncomputable def W (s₀ s' : S) : ℝ := ∑ a : A, π θ s₀ a * P s₀ a s'

/-- The time-0 visitation term collapses to the start state. -/
lemma rho_zero_sum (s₀ : S) (g : S → ℝ) :
    (∑ s : S, pgRho P π 0 s₀ θ s * g s) = g s₀ := by
  have heach : ∀ s : S, pgRho P π 0 s₀ θ s * g s = if s = s₀ then g s else 0 := by
    intro s
    rw [show pgRho P π 0 s₀ θ s = if s = s₀ then 1 else 0 from rfl]
    split <;> simp
  rw [Finset.sum_congr rfl (fun s _ => heach s), Finset.sum_ite_eq' Finset.univ s₀ g]
  simp

/-- Chapman–Kolmogorov sum-swap: peeling off the first step of `pgRho` and summing
`g` against it is the same as first transitioning from `s₀` and then summing `g`
against the remaining `ρ`. -/
lemma rho_succ_sum (s₀ : S) (t : ℕ) (g : S → ℝ) :
    (∑ s : S, pgRho P π (t + 1) s₀ θ s * g s)
      = ∑ s' : S, W P π θ s₀ s' * ∑ s : S, pgRho P π t s' θ s * g s := by
  -- LHS = ∑_s (∑_{s'} W(s₀,s') ρ_t(s',s)) g(s) = ∑_s ∑_{s'} W ρ g = ∑_{s'} ∑_s W ρ g = ∑_{s'} W ∑_s ρ g.
  calc (∑ s : S, pgRho P π (t + 1) s₀ θ s * g s)
      = ∑ s : S, (∑ s' : S, W P π θ s₀ s' * pgRho P π t s' θ s) * g s := by
        apply Finset.sum_congr rfl; intro s _
        rw [show pgRho P π (t + 1) s₀ θ s = ∑ s' : S, W P π θ s₀ s' * pgRho P π t s' θ s from rfl]
    _ = ∑ s : S, ∑ s' : S, W P π θ s₀ s' * pgRho P π t s' θ s * g s := by
        apply Finset.sum_congr rfl; intro s _; exact Finset.sum_mul Finset.univ _ (g s)
    _ = ∑ s' : S, ∑ s : S, W P π θ s₀ s' * pgRho P π t s' θ s * g s := Finset.sum_comm
    _ = ∑ s' : S, W P π θ s₀ s' * ∑ s : S, pgRho P π t s' θ s * g s := by
        apply Finset.sum_congr rfl; intro s' _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring

/-- Rewrite the `∑_a π · ∑_{s'} P · X(s')` structure into `∑_{s'} W(s₀,s') X(s')`. -/
lemma bellman_transition_rewrite (s₀ : S) (X : S → ℝ) :
    (∑ a : A, π θ s₀ a * ∑ s' : S, P s₀ a s' * X s')
      = ∑ s' : S, W P π θ s₀ s' * X s' := by
  calc (∑ a : A, π θ s₀ a * ∑ s' : S, P s₀ a s' * X s')
      = ∑ a : A, ∑ s' : S, π θ s₀ a * (P s₀ a s' * X s') := by
        apply Finset.sum_congr rfl; intro a _; exact Finset.mul_sum Finset.univ _ (π θ s₀ a)
    _ = ∑ s' : S, ∑ a : A, π θ s₀ a * (P s₀ a s' * X s') := Finset.sum_comm
    _ = ∑ s' : S, W P π θ s₀ s' * X s' := by
        apply Finset.sum_congr rfl; intro s' _
        rw [W, Finset.sum_mul]; apply Finset.sum_congr rfl; intro a _; ring

/-- Swap a weighted finite sum: `∑_x w(x) · ∑_i g(x,i) = ∑_i ∑_x w(x) · g(x,i)`. -/
lemma mul_sum_comm {ι : Type} (c : Finset ι) (w : S → ℝ) (g : S → ι → ℝ) :
    (∑ x : S, w x * ∑ i ∈ c, g x i) = ∑ i ∈ c, ∑ x : S, w x * g x i := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _; exact Finset.mul_sum c (g x) (w x)

end PGUnroll

open PGUnroll

/-- Full finite-horizon policy gradient theorem, by induction on the horizon `T`:
unroll `pg_bellman_step` and use the first-step recursion of `pgRho`. -/
theorem solution : ∀ {S A : Type} [Fintype S] [Fintype A] [DecidableEq S] (P : S → A → S → ℝ) (r : S → A → ℝ) (π : ℝ → S → A → ℝ) (θ : ℝ) (hdiff : ∀ s a, DifferentiableAt ℝ (fun θ' => π θ' s a) θ) (T : ℕ) (s₀ : S), deriv (fun θ' => pgValue P r π T θ' s₀) θ = ∑ t ∈ Finset.range T, ∑ s : S, pgRho P π t s₀ θ s * ∑ a : A, pgQ P r π (T - 1 - t) θ s a * deriv (fun θ' => π θ' s a) θ := by
  intro S A _ _ _ P r π θ hdiff T
  induction T with
  | zero =>
    intro s₀
    simp only [Finset.range_zero, Finset.sum_empty]
    have h0 : (fun θ' => pgValue P r π 0 θ' s₀) = (fun _ => (0 : ℝ)) := by ext x; rfl
    rw [h0, deriv_const]
  | succ T ih =>
    intro s₀
    -- Bellman step + IH.  LHS = Φ(T)(s₀) + ∑_a π ∑_{s'} P · ∑_t ∑_s ρ_t(s',s) Φ(T-1-t)(s).
    rw [pg_bellman_step P r π θ hdiff T s₀]
    -- Goal after pg_bellman_step + rewriting deriv V_T via ih:
    calc
      (∑ a : A, pgQ P r π T θ s₀ a * deriv (fun θ' => π θ' s₀ a) θ)
        + ∑ a : A, π θ s₀ a * ∑ s' : S, P s₀ a s' * deriv (fun θ' => pgValue P r π T θ' s') θ
      = Φ P r π θ T s₀
        + ∑ a : A, π θ s₀ a * ∑ s' : S, P s₀ a s' *
            (∑ t ∈ Finset.range T, ∑ s : S, pgRho P π t s' θ s * Φ P r π θ (T - 1 - t) s) := by
        congr 1
        apply Finset.sum_congr rfl; intro a _; congr 1
        apply Finset.sum_congr rfl; intro s' _; congr 1
        rw [ih s']; rfl
      _ = Φ P r π θ T s₀
        + ∑ s' : S, W P π θ s₀ s' *
            (∑ t ∈ Finset.range T, ∑ s : S, pgRho P π t s' θ s * Φ P r π θ (T - 1 - t) s) := by
        congr 1
        exact bellman_transition_rewrite P π θ s₀ _
      _ = Φ P r π θ T s₀
        + ∑ t ∈ Finset.range T, ∑ s' : S, W P π θ s₀ s' *
            (∑ s : S, pgRho P π t s' θ s * Φ P r π θ (T - 1 - t) s) := by
        congr 1
        exact mul_sum_comm (Finset.range T) (W P π θ s₀)
          (fun s' t => ∑ s : S, pgRho P π t s' θ s * Φ P r π θ (T - 1 - t) s)
      _ = Φ P r π θ T s₀
        + ∑ t ∈ Finset.range T, ∑ s : S, pgRho P π (t + 1) s₀ θ s * Φ P r π θ (T - 1 - t) s := by
        congr 1
        apply Finset.sum_congr rfl; intro t _
        exact (rho_succ_sum P π θ s₀ t _).symm
      _ = (∑ s : S, pgRho P π 0 s₀ θ s * Φ P r π θ T s)
        + ∑ t ∈ Finset.range T, ∑ s : S, pgRho P π (t + 1) s₀ θ s * Φ P r π θ (T - 1 - t) s := by
        congr 1
        exact (rho_zero_sum P π θ s₀ (Φ P r π θ T)).symm
      _ = ∑ t ∈ Finset.range (T + 1), ∑ s : S, pgRho P π t s₀ θ s * Φ P r π θ (T - t) s := by
        rw [Finset.sum_range_succ']
        have h1 : (∑ s : S, pgRho P π 0 s₀ θ s * Φ P r π θ (T - 0) s)
            = ∑ s : S, pgRho P π 0 s₀ θ s * Φ P r π θ T s := by
          apply Finset.sum_congr rfl; intro s _; congr 1
        have h2 : (∑ t ∈ Finset.range T, ∑ s : S, pgRho P π (t + 1) s₀ θ s * Φ P r π θ (T - (t + 1)) s)
            = ∑ t ∈ Finset.range T, ∑ s : S, pgRho P π (t + 1) s₀ θ s * Φ P r π θ (T - 1 - t) s := by
          apply Finset.sum_congr rfl; intro t _
          apply Finset.sum_congr rfl; intro s _
          congr 2
          omega
        rw [h1, h2]
        ring
      _ = ∑ t ∈ Finset.range (T + 1), ∑ s : S, pgRho P π t s₀ θ s
          * ∑ a : A, pgQ P r π (T + 1 - 1 - t) θ s a * deriv (fun θ' => π θ' s a) θ := rfl
