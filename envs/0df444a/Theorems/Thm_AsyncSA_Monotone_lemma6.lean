-- Prove2me | Theorems.Thm_AsyncSA_Monotone_lemma6
-- name    : AsyncSA.Monotone.lemma6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:50.241985+00:00
-- url     : https://prove2.me/theorems/2327f265-3c38-4c48-8a1f-9d9ffdbff999
-- title:
--   Lemma 6 — on a sample path, x_i(t) ≤ X_i(t) + W_i(t; t′_k) for all t ≥ t′_k
-- statement:
--   This is a statement about one fixed sample path of the asynchronous algorithm $x_i(t+1)=x_i(t)+\alpha_i(t)\bigl(F_i(x^i(t))-x_i(t)+w_i(t)\bigr)$, $x^i(t)=(x_1(\tau^i_1(t)),\dots,x_n(\tau^i_n(t)))$, with $\alpha_i(t)\in[0,1]$ and $\tau^i_j(t)\le t$.
--
--   Let $F$ satisfy Assumption 4 with fixed point $x^*$, let $r>0$, and let $U^k,L^k$ be the sequences of (16)–(17) started from $x^*\pm re$. Fix $k$ and times $t_k,t'_k$ such that
--
--   1. (18) $L^k\le x(t)\le U^k$ for all $t\ge t_k$;
--   2. $\tau^i_j(t)\ge t_k$ for all $t\ge t'_k$ and all $i,j$.
--
--   Define $W_i(t;t'_k)$ by $W_i(t'_k;t'_k)=0$ and $W_i(t+1;t'_k)=(1-\alpha_i(t))W_i(t;t'_k)+\alpha_i(t)w_i(t)$ for $t\ge t'_k$, and let $X_i(t)$, $t\ge t'_k$, satisfy $X_i(t'_k)=U^k_i$ and
--   $$
--   X_i(t+1)=(1-\alpha_i(t))X_i(t)+\alpha_i(t)F_i(U^k),\qquad t\ge t'_k .
--   $$
--   Then for every $i$,
--   $$
--   x_i(t)\le X_i(t)+W_i(t;t'_k)\qquad\text{for all }t\ge t'_k .
--   $$
--
--   This is the comparison step of the induction in the proof of Theorem 2: past $t'_k$ the iterate is dominated by a deterministic relaxation towards $F(U^k)$ plus the accumulated noise.
--
--   **Formalization Note** The lemma is pathwise: the sample path $\omega$, the index $k$, the times $t_k,t'_k$ and the sequence $X$ are given, with exactly the properties the paper has established at that point of the induction (no probabilistic quantifier appears). The bound (19) $L^k\le x^i(t)\le U^k$ for $t\ge t'_k$ is not assumed separately, since the paper derives it ("In particular") from (18) and the choice of $t'_k$. $W_i(t;t'_k)$ is `tailW` applied to the path's $\alpha_i(\cdot)$ and $w_i(\cdot)$. Components are indexed by `Fin n` (0-based).
-- source:
--   Tsitsiklis, Asynchronous Stochastic Approximation and Q-Learning, Machine Learning 16 (1994), p. 194, §5, Lemma 6 (with (18)–(21), pp. 193–194)

import Mathlib
import Definitions.Def_AsyncSA_Monotone_Model

namespace AsyncSA.Monotone

theorem lemma6 {n : ℕ} {Ω : Type*} (alg : Algorithm n Ω) (xstar : Fin n → ℝ) (r : ℝ)
    (h4 : Assumption4 alg.F xstar) (hr : 0 < r) (ω : Ω) (k tk t'k : ℕ)
    (h18 : ∀ t, tk ≤ t →
      Lseq alg.F xstar r k ≤ alg.x t ω ∧ alg.x t ω ≤ Useq alg.F xstar r k)
    (hτ : ∀ t, t'k ≤ t → ∀ i j, tk ≤ alg.τ i j t ω)
    (X : Fin n → ℕ → ℝ)
    (hX0 : ∀ i, X i t'k = Useq alg.F xstar r k i)
    (hX : ∀ i t, t'k ≤ t →
      X i (t + 1) = (1 - alg.α i t ω) * X i t + alg.α i t ω * alg.F (Useq alg.F xstar r k) i) :
    ∀ i, ∀ t, t'k ≤ t →
      alg.x t ω i ≤ X i t + tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) t'k t := by sorry

end AsyncSA.Monotone
