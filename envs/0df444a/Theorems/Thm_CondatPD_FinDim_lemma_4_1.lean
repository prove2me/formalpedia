-- Prove2me | Theorems.Thm_CondatPD_FinDim_lemma_4_1
-- name    : CondatPD.FinDim.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:19:46.52291+00:00
-- url     : https://prove2.me/theorems/f5d24b29-c187-483c-ac4b-991377a46a05
-- title:
--   Lemma 4.1 (Krasnosel'skii–Mann iteration), p. 8 — inexact relaxed iterates of a nonexpansive T converge weakly to a fixed point
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $T:\mathcal H\to\mathcal H$ nonexpansive, i.e. $\|T(s)-T(s')\|\le\|s-s'\|$. Let $(\rho_n)$ be a sequence in $]0,1[$ and $(e_n)$ a sequence in $\mathcal H$. Suppose that $\operatorname{fix}(T)\neq\emptyset$,
--   $$\sum_{n\in\mathbb N}\rho_n(1-\rho_n)=+\infty\qquad\text{and}\qquad\sum_{n\in\mathbb N}\rho_n\|e_n\|<+\infty .$$
--   Let $s_0\in\mathcal H$ and $s_{n+1}=s_n+\rho_n\big(T(s_n)+e_n-s_n\big)$ for every $n$ (13). Then $(s_n)$ converges weakly to some $\hat s\in\operatorname{fix}(T)$: $\langle s_n,v\rangle\to\langle\hat s,v\rangle$ for every $v\in\mathcal H$.
--
--   In the proof of Theorem 3.3 this lemma is applied, after a change of variables, to the shadow iteration (34) of the firmly nonexpansive operator $T'=S\circ T$.
--
--   **Formalization Note** $\sum\rho_n(1-\rho_n)=+\infty$ is stated as divergence of the partial sums to $+\infty$, and $\sum\rho_n\|e_n\|<+\infty$ as summability of the nonnegative series.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), p. 8, Lemma 4.1, (13)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_Nonexpansive
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence

open InnerProductSpace Filter Topology

namespace CondatPD.FinDim

/-- Lemma 4.1 (Krasnosel'skii–Mann iteration), p. 8: inexact relaxed iterates of a nonexpansive
operator with a fixed point converge weakly to a fixed point. -/
theorem lemma_4_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E → E) (hT : ThreeOpSplitting.Convergence.IsNonexpansive T)
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 < ρ n ∧ ρ n < 1) (e : ℕ → E)
    (hfix : ∃ s : E, T s = s)
    (hdiv : Tendsto (fun N => ∑ n ∈ Finset.range N, ρ n * (1 - ρ n)) atTop atTop)
    (hsum : Summable (fun n => ρ n * ‖e n‖))
    (s : ℕ → E) (hs : ∀ n, s (n + 1) = s n + ρ n • (T (s n) + e n - s n)) :
    ∃ sh : E, T sh = sh ∧ ThreeOpSplitting.Convergence.WeakTendsto s sh := by sorry

end CondatPD.FinDim
