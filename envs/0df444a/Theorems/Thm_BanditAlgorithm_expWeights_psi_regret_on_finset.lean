-- Prove2me | Theorems.Thm_BanditAlgorithm_expWeights_psi_regret_on_finset
-- name    : BanditAlgorithm.expWeights_psi_regret_on_finset
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T17:28:08.410242+00:00
-- url     : https://prove2.me/theorems/c28315e9-377f-4aa3-8bdc-e4c5f97d0ece
-- title:
--   Exponential-weights Psi regret bound on a finite comparator set
-- statement:
--   Let S be a nonempty finite set of experts, let eta be positive, and let y_{t,a} be arbitrary real-valued loss estimates. Define exponential-weights probabilities Q_t on S using the cumulative estimates before round t. Then every comparator a_0 in S satisfies
--
--   $$
--   \sum_{t<n}\sum_a Q_{t,a}(y_{t,a}-y_{t,a_0}) \leq \frac{\log |S|}{\eta}+\frac1\eta\sum_{t<n}\sum_a Q_{t,a}\bigl(e^{-\eta y_{t,a}}+\eta y_{t,a}-1\bigr).
--   $$
--
--   This finite-support form of the exponential-weights potential inequality is the deterministic online-learning ingredient used by Algorithm 26.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Chapter 37, equation (37.11), printed p. 493, https://tor-lattimore.com/downloads/book/book.pdf

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Order

open scoped BigOperators

namespace BanditAlgorithm

/-! Lattimore--Szepesvári, Eq. (37.11), printed p. 493, restricted to
the finite comparator set used by Algorithm 26. -/

theorem expWeights_psi_regret_on_finset
    {k : ℕ} (S : Finset (Fin k)) (hS : S.Nonempty)
    (n : ℕ) (η : ℝ) (hη : 0 < η) (y : ℕ → Fin k → ℝ) :
    let W := fun t : ℕ ↦
      ∑ a ∈ S, Real.exp (- (η * ∑ s ∈ Finset.range t, y s a))
    let Q := fun t : ℕ ↦ fun a : Fin k ↦
      if a ∈ S then Real.exp (- (η * ∑ s ∈ Finset.range t, y s a)) / W t else 0
    ∀ a₀ ∈ S,
      (∑ t ∈ Finset.range n, ∑ a : Fin k, Q t a * (y t a - y t a₀)) ≤
        Real.log S.card / η + (1 / η) *
          ∑ t ∈ Finset.range n, ∑ a : Fin k,
            Q t a * (Real.exp (-η * y t a) + η * y t a - 1) := by
  sorry
