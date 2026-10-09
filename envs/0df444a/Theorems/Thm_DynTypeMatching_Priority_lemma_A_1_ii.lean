-- Prove2me | Theorems.Thm_DynTypeMatching_Priority_lemma_A_1_ii
-- name    : DynTypeMatching.Priority.lemma_A_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:54:43.409434+00:00
-- url     : https://prove2.me/theorems/ac9bd871-6bc7-45e3-89d6-296152c1e7b0
-- title:
--   Lemma A.1(ii), Online Appendix A, p. 1 — shifting ε of supply from type j to type j′ costs at most a weighted sum of reward gaps
-- statement:
--   Consider a well-posed dynamic type matching model with supply carry-over fraction $\beta>0$. Let $1\le t\le T+1$, let $(\mathbf x,\mathbf y)$ be a nonnegative state, let $j,j'$ be supply types with $y_j>0$, and let $\varepsilon\in[0,y_j]$. Then there are nonnegative numbers $\xi^\tau_{i'}$ ($\tau=t,\dots,T$, $i'\in\mathcal D$) such that
--   $$\sum_{\tau=t}^T\beta^{-(\tau-t)}\sum_{i'=1}^m\xi^\tau_{i'}\le\varepsilon$$
--   and
--   $$V_t(\mathbf x,\mathbf y-\varepsilon\mathbf e^n_j+\varepsilon\mathbf e^n_{j'})-V_t(\mathbf x,\mathbf y)\ \ge\ -\sum_{\tau=t}^T\sum_{i'=1}^m\xi^\tau_{i'}\big(r^\tau_{i'j}-r^\tau_{i'j'}\big).$$
--   Here $\mathbf e^n_j$ is the $j$-th unit vector of $\mathbb R^n$. For $t=T+1$ the sums are empty.
--
--   This is the supply-side counterpart of Lemma A.1(i), used for row dominance in Lemma A.2(ii).
--
--   **Formalization Note** The page prints the sums up to $n$ over demand types and the unit vector $\mathbf e^m_j$; the multipliers are indexed by the $m$ demand types and the unit vector lives in $\mathbb R^n$. The hypothesis $\beta>0$ is added because $\beta^{-(\tau-t)}$ is undefined at $\beta=0$.
-- source:
--   Hu, Zhou, Dynamic Type Matching, arXiv:1811.07048v1, Online Appendix A, p. 1, Lemma A.1(ii)

import Mathlib
import Definitions.Def_DynTypeMatching_Priority_Model

namespace DynTypeMatching.Priority
theorem lemma_A_1_ii {m n : ℕ} (M : Model m n) (hM : M.WellPosed) (hβ : 0 < M.β)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ M.T + 1) (x : Fin m → ℝ) (y : Fin n → ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (j j' : Fin n) (hyj : 0 < y j) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hεy : ε ≤ y j) :
    ∃ xi : ℕ → Fin m → ℝ, (∀ τ i, 0 ≤ xi τ i) ∧
      ∑ τ ∈ Finset.Icc t M.T, (M.β ^ (τ - t))⁻¹ * ∑ i, xi τ i ≤ ε ∧
      -(∑ τ ∈ Finset.Icc t M.T, ∑ i, xi τ i * (M.r τ i j - M.r τ i j')) ≤
        V M t x (y - ε • (Pi.single j (1 : ℝ) : Fin n → ℝ) + ε • (Pi.single j' (1 : ℝ) : Fin n → ℝ)) -
          V M t x y := by sorry
end DynTypeMatching.Priority
