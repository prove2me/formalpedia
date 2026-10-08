-- Prove2me | Theorems.Thm_AsyncSA_Contraction_lemma3
-- name    : AsyncSA.Contraction.lemma3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:53.94333+00:00
-- url     : https://prove2.me/theorems/0d3adabf-40b0-4eac-a717-c528bde7abca
-- title:
--   Lemma 3 — pathwise bounds in the boundedness argument
-- statement:
--   Fix a sample path in the proof of Theorem 1. Let $M(t)=\max_{s\le t,j}|x_j(s)|$ and let $G(t)$ be the paper's auxiliary envelope with parameters $G_0>0$, $0\le\gamma<1$, and $\epsilon>0$ satisfying $\gamma(1+\epsilon)=1$. Assume the growth estimate $|F_i(y)|\le\gamma\max\{\max_j|y_j|,G_0\}$, the stated update rule for $G$, and a time $t_0$ at which $M(t_0)\le G(t_0)$ and every rescaled noise tail $\widetilde W_i(t;t_0)$ has absolute value at most $\epsilon$ for $t\ge t_0$. Under the paper's contradiction assumption that the iterate path is unbounded, for every $t\ge t_0$ and coordinate $i$,
--
--   $$G(t)=G(t_0),\qquad -G(t_0)(1+\epsilon)\le-G(t_0)+\widetilde W_i(t;t_0)G(t_0)\le x_i(t)\le G(t_0)+\widetilde W_i(t;t_0)G(t_0)\le G(t_0)(1+\epsilon).$$
--
--   This is the pathwise estimate used in the proof of almost-sure boundedness.
--
--   **Formalization Note** The theorem fixes one sample path after the null set has been discarded. The paper constructs $G$ in §4; the Lean statement characterizes that sequence by its initial value and two update cases. The exponent $k-1$ is natural-number subtraction, but the jump case forces $k>0$.
-- source:
--   Tsitsiklis, Asynchronous Stochastic Approximation and Q-Learning, Machine Learning 16 (1994), pp. 191–192, §4, equations (11)–(15), Lemma 3

import Mathlib
import Definitions.Def_AsyncSA_Contraction_Model

namespace AsyncSA.Contraction

open MeasureTheory Filter Topology

/-- Lemma 3, p. 192, on a retained sample path of the proof of Theorem 1. -/
theorem lemma3 {n : ℕ} {Ω : Type*} (alg : Algorithm n Ω) (ω : Ω)
    (γ G₀ ε : ℝ) (G : ℕ → ℝ) (t₀ : ℕ)
    (hγ : 0 ≤ γ ∧ γ < 1) (hG₀ : 0 < G₀) (hε : 0 < ε)
    (hγε : γ * (1 + ε) = 1)
    (hF : ∀ x : Fin n → ℝ, ∀ i,
      |alg.F x i| ≤ γ * max (⨆ j : Fin n, |x j|) G₀)
    (hGinit : G 0 = max (alg.runMax 0 ω) G₀)
    (hGstay : ∀ t, alg.runMax (t + 1) ω ≤ (1 + ε) * G t → G (t + 1) = G t)
    (hGjump : ∀ t, (1 + ε) * G t < alg.runMax (t + 1) ω →
      ∃ k : ℕ, G (t + 1) = G₀ * (1 + ε) ^ k ∧
        G₀ * (1 + ε) ^ (k - 1) < alg.runMax (t + 1) ω ∧
        alg.runMax (t + 1) ω ≤ G₀ * (1 + ε) ^ k)
    (hM₀ : alg.runMax t₀ ω ≤ G t₀)
    (hW : ∀ t ≥ t₀, ∀ i : Fin n,
      |tailW (fun s => alg.α i s ω)
        (fun s => alg.w i s ω / G s) t₀ t| ≤ ε)
    (hunbounded : ¬ ∃ M : ℝ, ∀ t j, |alg.x t ω j| ≤ M) :
    ∀ t ≥ t₀, G t = G t₀ ∧ ∀ i : Fin n,
      let W := tailW (fun s => alg.α i s ω)
        (fun s => alg.w i s ω / G s) t₀ t;
      -(G t₀ * (1 + ε)) ≤ -G t₀ + W * G t₀ ∧
        -G t₀ + W * G t₀ ≤ alg.x t ω i ∧
        alg.x t ω i ≤ G t₀ + W * G t₀ ∧
        G t₀ + W * G t₀ ≤ G t₀ * (1 + ε) := by sorry

end AsyncSA.Contraction
