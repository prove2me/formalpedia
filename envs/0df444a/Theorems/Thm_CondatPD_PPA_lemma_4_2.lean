-- Prove2me | Theorems.Thm_CondatPD_PPA_lemma_4_2
-- name    : CondatPD.PPA.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:15:36.380462+00:00
-- url     : https://prove2.me/theorems/2f34a3e0-33a8-4c40-9dc9-5f6ef563a8a6
-- title:
--   Lemma 4.2 (Proximal point algorithm), p. 9 — relaxed inexact proximal iterates converge weakly to a zero of M
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $M:\mathcal H\rightrightarrows\mathcal H$ a maximally monotone operator with resolvent $(I+M)^{-1}$. Let $(\rho_n)_{n\in\mathbb N}$ be a sequence in $]0,2[$ and $(e_n)_{n\in\mathbb N}$ a sequence in $\mathcal H$. Suppose that $\mathrm{zer}(M)=\{u:0\in Mu\}\neq\emptyset$, that
--   $$\sum_{n\in\mathbb N}\rho_n(2-\rho_n)=+\infty\qquad\text{and}\qquad\sum_{n\in\mathbb N}\rho_n\|e_n\|<+\infty .$$
--   Let $s_0\in\mathcal H$ and let $(s_n)$ satisfy, for every $n$,
--   $$s_{n+1}=s_n+\rho_n\big((I+M)^{-1}(s_n)+e_n-s_n\big).\qquad(14)$$
--   Then $(s_n)$ converges weakly to some $\hat s\in\mathrm{zer}(M)$.
--
--   In the proof of Theorem 3.2, Algorithm 3.1 with $F=0$ is exactly this iteration for $M=P^{-1}\circ A$ in the Hilbert space $\mathcal Z_P$.
--
--   **Formalization Note** The resolvent enters as a map $J:\mathcal H\to\mathcal H$ with $x-Jx\in M(Jx)$ for every $x$ (the published `IsResolvent 1 M J`); for maximally monotone $M$ such a map exists and is unique (Minty). The series conditions are encoded as in Lemma 4.1. This lemma is not the published Eckstein–Bertsekas Theorem 3, which assumes $\inf\rho_n>0$, $\sup\rho_n<2$ and unweighted summable errors.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), p. 9, Lemma 4.2, (14)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence

open Filter Topology

namespace CondatPD.PPA

theorem lemma_4_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (M : H → Set H) (hM : ThreeOpSplitting.Convergence.IsMaximalMonotone M)
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 < ρ n ∧ ρ n < 2) (e : ℕ → H)
    (hzer : (ThreeOpSplitting.Convergence.zer M).Nonempty)
    (hsum : Tendsto (fun N => ∑ n ∈ Finset.range N, ρ n * (2 - ρ n)) atTop atTop)
    (herr : Summable (fun n => ρ n * ‖e n‖))
    (J : H → H) (hJ : ThreeOpSplitting.Convergence.IsResolvent 1 M J)
    (s : ℕ → H) (hs : ∀ n, s (n + 1) = s n + ρ n • (J (s n) + e n - s n)) :
    ∃ sh ∈ ThreeOpSplitting.Convergence.zer M, ThreeOpSplitting.Convergence.WeakTendsto s sh := by sorry

end CondatPD.PPA
