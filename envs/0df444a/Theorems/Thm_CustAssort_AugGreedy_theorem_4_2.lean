-- Prove2me | Theorems.Thm_CustAssort_AugGreedy_theorem_4_2
-- name    : CustAssort.AugGreedy.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:48:53.901917+00:00
-- url     : https://prove2.me/theorems/ac8335ff-1a45-4f19-af42-39913a56c3e0
-- title:
--   Theorem 4.2 — Augmented Greedy recovers a $(1-1/e)$ fraction of complete-type revenue
-- statement:
--   Consider CAP with positive product revenues ordered from highest to lowest, nonnegative MNL preference weights, and nonnegative type-arrival probabilities summing to one. Let $S^*$ be an optimal first-stage assortment under capacity $K$. For customer types $C$, products $P$, and any $k\ge|P\cap S^*|$, let $\Delta$ be any output of Augmented Greedy on $C,k$. A type is complete with respect to $P$ when every product of $P\cap S^*$ belongs to its threshold optimal personalized assortment. Write $C_P$ for the complete types in $C$. Then
--   $$
--   f^C(\Delta)\ge(1-1/e)\,f^{C_P}(P\cap S^*).
--   $$
--   This structural bound is the paper's guarantee for Augmented Greedy and a building block for its later CAP approximation results.
--
--   **Formalization Note** The theorem covers every legal Greedy run and every tie-breaking choice of Augmented Greedy. The threshold optimal assortment is $\{i\in S^*:r_i\ge f_j(S^*)\}$, as in Lemma E.1. $k$ is independent of $K$.
-- source:
--   El Housni & Topaloglu, Joint Assortment Optimization and Customization under a Mixture of Multinomial Logit Models: Value of Personalized Assortments, SSRN 3830082, https://ssrn.com/abstract=3830082 (version of December 7, 2021), Definition 4.1 and Theorem 4.2, p. 11; proof pp. 11–12

import Mathlib
import Definitions.Def_CustAssort_AugGreedy_Setting

namespace CustAssort.AugGreedy

/-- Theorem 4.2, p. 11: Augmented Greedy captures a 1−1/e fraction of complete-type revenue. -/
theorem theorem_4_2 {n m : ℕ} (θ : Fin m → ℝ) (v : Fin n → Fin m → ℝ)
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (hv : ∀ i j, 0 ≤ v i j)
    (hθ : ∀ j, 0 ≤ θ j) (hθsum : ∑ j, θ j = 1) (hanti : Antitone r)
    (K : ℕ) (Sstar : Finset (Fin n)) (hS : IsCAPOpt θ v r K Sstar)
    (C : Finset (Fin m)) (P : Finset (Fin n)) (k : ℕ)
    (hk : (P ∩ Sstar).card ≤ k) (Δ : Finset (Fin n))
    (hΔ : IsAugGreedyOutput θ v r C k Δ) :
    (1 - Real.exp (-1)) *
      fC θ v r (completeTypes v r Sstar C P) (P ∩ Sstar) ≤ fC θ v r C Δ := by sorry

end CustAssort.AugGreedy
