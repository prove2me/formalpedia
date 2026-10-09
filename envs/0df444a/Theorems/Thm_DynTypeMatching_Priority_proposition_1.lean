-- Prove2me | Theorems.Thm_DynTypeMatching_Priority_proposition_1
-- name    : DynTypeMatching.Priority.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:15.790524+00:00
-- url     : https://prove2.me/theorems/15931266-9f9a-4c0a-9d37-d0168565e262
-- title:
--   Proposition 1, p. 10 — H_t and V_t are continuous and concave, and an optimal matching policy exists
-- statement:
--   Let a well-posed dynamic type matching model be given (horizon $T$, rewards $r^t_{ij}$, carry-over fractions $\alpha,\beta\in[0,1]$, integrable nonnegative arrivals). Then:
--
--   1. for every $1\le t\le T+1$, the value function $(\mathbf x,\mathbf y)\mapsto V_t(\mathbf x,\mathbf y)$ is concave and continuous on the orthant $\mathbb R^m_+\times\mathbb R^n_+$;
--   2. for every $1\le t\le T$, the map $(\mathbf Q,\mathbf x,\mathbf y)\mapsto H_t(\mathbf Q,\mathbf x,\mathbf y)$ is concave and continuous on the feasibility set
--      $$\{(\mathbf Q,\mathbf x,\mathbf y)\ :\ \mathbf Q\ge0,\ \mathbf x-\mathbf 1^m\mathbf Q^{\mathsf T}\ge0,\ \mathbf y-\mathbf 1^n\mathbf Q\ge0\};$$
--   3. there exists an optimal matching policy $P^*=\{\mathbf Q^*_t(\mathbf x,\mathbf y)\}_{t=1,\dots,T}$.
--
--   This is the existence result on which every structural property of the optimal policy is built: the priority theorems select, among optimal decisions, ones with additional structure.
--
--   **Formalization Note** The page states continuity and concavity without a domain; the natural one is where (1) is defined, namely states in the nonnegative orthant and feasible triples $(\mathbf Q,\mathbf x,\mathbf y)$ (outside it the real supremum takes a junk value). The integrability of the arrivals, part of the well-posedness hypothesis, is what makes the expectation in (1) well defined. This version of the paper prints no proof of Proposition 1.
-- source:
--   Hu, Zhou, Dynamic Type Matching, arXiv:1811.07048v1, p. 10, Proposition 1

import Mathlib
import Definitions.Def_DynTypeMatching_Priority_Model

namespace DynTypeMatching.Priority
theorem proposition_1 {m n : ℕ} (M : Model m n) (hM : M.WellPosed) :
    (∀ t, 1 ≤ t → t ≤ M.T + 1 →
      ConcaveOn ℝ {p : (Fin m → ℝ) × (Fin n → ℝ) | 0 ≤ p.1 ∧ 0 ≤ p.2}
          (fun p => V M t p.1 p.2) ∧
        ContinuousOn (fun p : (Fin m → ℝ) × (Fin n → ℝ) => V M t p.1 p.2)
          {p | 0 ≤ p.1 ∧ 0 ≤ p.2}) ∧
    (∀ t, 1 ≤ t → t ≤ M.T →
      ConcaveOn ℝ {p : (Fin m → Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ) | Feasible p.2.1 p.2.2 p.1}
          (fun p => H M t p.1 p.2.1 p.2.2) ∧
        ContinuousOn (fun p : (Fin m → Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ) =>
            H M t p.1 p.2.1 p.2.2)
          {p | Feasible p.2.1 p.2.2 p.1}) ∧
    (∃ P : ℕ → (Fin m → ℝ) → (Fin n → ℝ) → (Fin m → Fin n → ℝ), IsOptimalPolicy M P) := by sorry
end DynTypeMatching.Priority
