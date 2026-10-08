-- Prove2me | Theorems.Thm_AsyncSA_Contraction_lemma8
-- name    : AsyncSA.Contraction.lemma8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:10.022535+00:00
-- url     : https://prove2.me/theorems/7f56e716-7de8-4798-8141-b363506c5102
-- title:
--   Lemma 8 — coordinate comparison with a noise tail
-- statement:
--   Fix a sample path after translating the fixed point to zero and scaling coordinates so the weight vector is all ones. Let $D_k\ge0$ be an eventual bound on the iterates from time $t_k$, and choose $\tau_k\ge t_k$ so that every outdated input vector $x^i(t)$ is bounded by $D_k$ after $\tau_k$. Suppose $\|F(y)\|_\infty\le\beta\|y\|_\infty$ for $0\le\beta<1$. Let $Y_i(\tau_k)=D_k$ and $Y_i(t+1)=(1-\alpha_i(t))Y_i(t)+\alpha_i(t)\beta D_k$, and let $W_i(t;\tau_k)$ be the zero-start noise tail. Then, for every $i$ and $t\ge\tau_k$,
--
--   $$-Y_i(t)+W_i(t;\tau_k)\le x_i(t)\le Y_i(t)+W_i(t;\tau_k).$$
--
--   The comparison is the pathwise step used in the final convergence argument.
--
--   **Formalization Note** The paper obtains the setting after normalization on p. 195. The bound $|W_i(t;\tau_k)|\le\beta\epsilon D_k$ is used after Lemma 8 and does not enter its comparison. In Lean the maximum norm is the norm on `Fin n → ℝ`.
-- source:
--   Tsitsiklis, Asynchronous Stochastic Approximation and Q-Learning, Machine Learning 16 (1994), pp. 195–196, §6, equations (22)–(25), Lemma 8

import Mathlib
import Definitions.Def_AsyncSA_Contraction_Model

namespace AsyncSA.Contraction

open MeasureTheory Filter Topology

/-- Lemma 8, p. 196, after the proof's translation and coordinate scaling. -/
theorem lemma8 {n : ℕ} {Ω : Type*} (alg : Algorithm n Ω) (ω : Ω)
    (β Dₖ : ℝ) (tₖ τₖ : ℕ) (Y : Fin n → ℕ → ℝ)
    (hβ : 0 ≤ β ∧ β < 1) (hDₖ : 0 ≤ Dₖ)
    (hF : ∀ y : Fin n → ℝ, ‖alg.F y‖ ≤ β * ‖y‖)
    (hτ : tₖ ≤ τₖ)
    (hx : ∀ t ≥ tₖ, ∀ j : Fin n, |alg.x t ω j| ≤ Dₖ)
    (hxi : ∀ t ≥ τₖ, ∀ i j : Fin n, |alg.xi i t ω j| ≤ Dₖ)
    (hYinit : ∀ i, Y i τₖ = Dₖ)
    (hYstep : ∀ i t, τₖ ≤ t →
      Y i (t + 1) = (1 - alg.α i t ω) * Y i t + alg.α i t ω * β * Dₖ) :
    ∀ i : Fin n, ∀ t ≥ τₖ,
      -Y i t + tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) τₖ t ≤
          alg.x t ω i ∧
        alg.x t ω i ≤
          Y i t + tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) τₖ t := by sorry

end AsyncSA.Contraction
