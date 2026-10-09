-- Prove2me | Theorems.Thm_DynTypeMatching_Priority_lemma_A_1_i
-- name    : DynTypeMatching.Priority.lemma_A_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:54:45.530988+00:00
-- url     : https://prove2.me/theorems/22e2b0fc-4fa7-41de-98e0-141a6231497b
-- title:
--   Lemma A.1(i), Online Appendix A, p. 1 — shifting ε of demand from type i to type i′ costs at most a weighted sum of reward gaps
-- statement:
--   Consider a well-posed dynamic type matching model with demand carry-over fraction $\alpha>0$. Let $1\le t\le T+1$, let $(\mathbf x,\mathbf y)$ be a nonnegative state, let $i,i'$ be demand types with $x_i>0$, and let $\varepsilon\in[0,x_i]$. Then there are nonnegative numbers $\lambda^\tau_{j'}$ ($\tau=t,\dots,T$, $j'\in\mathcal S$) such that
--   $$\sum_{\tau=t}^T\alpha^{-(\tau-t)}\sum_{j'=1}^n\lambda^\tau_{j'}\le\varepsilon$$
--   and
--   $$V_t(\mathbf x-\varepsilon\mathbf e^m_i+\varepsilon\mathbf e^m_{i'},\mathbf y)-V_t(\mathbf x,\mathbf y)\ \ge\ -\sum_{\tau=t}^T\sum_{j'=1}^n\lambda^\tau_{j'}\big(r^\tau_{ij'}-r^\tau_{i'j'}\big).$$
--   Here $\mathbf e^m_i$ is the $i$-th unit vector of $\mathbb R^m$. For $t=T+1$ the sums are empty and the statement reads $0\ge0$.
--
--   The lemma bounds the loss from relabelling $\varepsilon$ units of type-$i$ demand as type $i'$ by the reward gaps between $i$ and $i'$ along future matchings; it is the key estimate behind Lemma A.2.
--
--   **Formalization Note** The multipliers are indexed by supply types $j'=1,\dots,n$ (the page prints $\lambda^\tau_1,\dots,\lambda^\tau_m$ and $\sum_{j'=1}^m$) and the unit vector is $\mathbf e^m_i$ (the page prints $\mathbf e^n_i$). The hypothesis $\alpha>0$ is added: $\alpha^{-(\tau-t)}$ is undefined at $\alpha=0$, and in Lean $0^{-1}=0$ would silently drop the constraint on future multipliers.
-- source:
--   Hu, Zhou, Dynamic Type Matching, arXiv:1811.07048v1, Online Appendix A, p. 1, Lemma A.1(i)

import Mathlib
import Definitions.Def_DynTypeMatching_Priority_Model

namespace DynTypeMatching.Priority
theorem lemma_A_1_i {m n : ℕ} (M : Model m n) (hM : M.WellPosed) (hα : 0 < M.α)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ M.T + 1) (x : Fin m → ℝ) (y : Fin n → ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (i i' : Fin m) (hxi : 0 < x i) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hεx : ε ≤ x i) :
    ∃ lam : ℕ → Fin n → ℝ, (∀ τ j, 0 ≤ lam τ j) ∧
      ∑ τ ∈ Finset.Icc t M.T, (M.α ^ (τ - t))⁻¹ * ∑ j, lam τ j ≤ ε ∧
      -(∑ τ ∈ Finset.Icc t M.T, ∑ j, lam τ j * (M.r τ i j - M.r τ i' j)) ≤
        V M t (x - ε • (Pi.single i (1 : ℝ) : Fin m → ℝ) + ε • (Pi.single i' (1 : ℝ) : Fin m → ℝ)) y -
          V M t x y := by sorry
end DynTypeMatching.Priority
