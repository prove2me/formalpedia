-- Prove2me | Theorems.Thm_CondatPD_PPA_lemma_4_1
-- name    : CondatPD.PPA.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:15:29.163134+00:00
-- url     : https://prove2.me/theorems/2da81ccd-ed7b-4421-9f77-65d63d6acc0f
-- title:
--   Lemma 4.1 (Krasnosel'skii–Mann iteration), p. 8 — relaxed inexact iterates of a nonexpansive T converge weakly to a fixed point
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $T:\mathcal H\to\mathcal H$ nonexpansive, i.e. $\|Tx-Ty\|\le\|x-y\|$ for all $x,y$. Let $(\rho_n)_{n\in\mathbb N}$ be a sequence in $]0,1[$ and $(e_n)_{n\in\mathbb N}$ a sequence in $\mathcal H$. Suppose that $T$ has a fixed point, that
--   $$\sum_{n\in\mathbb N}\rho_n(1-\rho_n)=+\infty\qquad\text{and}\qquad\sum_{n\in\mathbb N}\rho_n\|e_n\|<+\infty .$$
--   Let $s_0\in\mathcal H$ and let $(s_n)$ satisfy, for every $n$,
--   $$s_{n+1}=s_n+\rho_n\big(T(s_n)+e_n-s_n\big).\qquad(13)$$
--   Then $(s_n)$ converges weakly to some fixed point $\hat s$ of $T$.
--
--   This is the inexact Krasnosel'skii–Mann theorem; in the paper it yields the proximal point Lemma 4.2, through which Theorem 3.2 is proved.
--
--   **Formalization Note** "$\sum\rho_n(1-\rho_n)=+\infty$" is stated as divergence of the partial sums to $+\infty$; "$\sum\rho_n\|e_n\|<+\infty$" as summability of a nonnegative series. Weak convergence is $\langle s_n,v\rangle\to\langle\hat s,v\rangle$ for every $v$.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), p. 8, Lemma 4.1, (13)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_Nonexpansive
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence

open Filter Topology

namespace CondatPD.PPA

theorem lemma_4_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → H) (hT : ThreeOpSplitting.Convergence.IsNonexpansive T)
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 < ρ n ∧ ρ n < 1) (e : ℕ → H)
    (hfix : ∃ s : H, T s = s)
    (hsum : Tendsto (fun N => ∑ n ∈ Finset.range N, ρ n * (1 - ρ n)) atTop atTop)
    (herr : Summable (fun n => ρ n * ‖e n‖))
    (s : ℕ → H) (hs : ∀ n, s (n + 1) = s n + ρ n • (T (s n) + e n - s n)) :
    ∃ sh : H, T sh = sh ∧ ThreeOpSplitting.Convergence.WeakTendsto s sh := by sorry

end CondatPD.PPA
