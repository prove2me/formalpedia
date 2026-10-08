-- Prove2me | Theorems.Thm_AsyncSA_Monotone_lemma7
-- name    : AsyncSA.Monotone.lemma7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:51.271141+00:00
-- url     : https://prove2.me/theorems/e8201042-fe07-4c4f-bb19-273eed02f926
-- title:
--   Lemma 7 — on a sample path, x_i(t) ≤ U_i^{k+1} for all i and t ≥ t″_k
-- statement:
--   This is a statement about one fixed sample path of the asynchronous algorithm $x_i(t+1)=x_i(t)+\alpha_i(t)\bigl(F_i(x^i(t))-x_i(t)+w_i(t)\bigr)$, $x^i(t)=(x_1(\tau^i_1(t)),\dots,x_n(\tau^i_n(t)))$, with $\alpha_i(t)\in[0,1]$ and $\tau^i_j(t)\le t$.
--
--   Let $F$ satisfy Assumption 4 with fixed point $x^*$, let $r>0$, and let $U^k,L^k$ be the sequences of (16)–(17) started from $x^*\pm re$. Fix $k$ and times $t_k,t'_k$ such that $L^k\le x(t)\le U^k$ for all $t\ge t_k$ (18) and $\tau^i_j(t)\ge t_k$ for all $t\ge t'_k$ and all $i,j$. Let $X_i$ be defined by $X_i(t'_k)=U^k_i$ and (21), and $W_i(t;t'_k)$ by (20), as in Lemma 6. Assume $U^k\ne F(U^k)$ and let
--   $$
--   \delta_k=\min\Bigl\{\tfrac14\bigl(U^k_i-F_i(U^k)\bigr)\;:\;U^k_i-F_i(U^k)>0\Bigr\}.
--   $$
--   Let $t''_k\ge t'_k$ be such that, for all $i$,
--   $$
--   \prod_{\tau=t'_k}^{t''_k-1}(1-\alpha_i(\tau))\le\frac14\qquad\text{and}\qquad W_i(t;t'_k)\le\delta_k\ \text{ for all }t\ge t''_k .
--   $$
--   Then
--   $$
--   x_i(t)\le U^{k+1}_i\qquad\text{for all }i\text{ and all }t\ge t''_k .
--   $$
--
--   This is the step that advances the upper half of the bracketing (18) from $U^k$ to $U^{k+1}$; the lower half is symmetric.
--
--   **Formalization Note** The lemma is pathwise, with the induction's objects ($\omega$, $k$, $t_k$, $t'_k$, $t''_k$, $X$, $\delta_k$) given and carrying exactly the properties the paper has established at that point. $\delta_k$ is given as the least element of the set $\{(U^k_i-F_i(U^k))/4 : U^k_i-F_i(U^k)>0\}$. The case $U^k=F(U^k)$, which the paper disposes of before the lemma ("We therefore assume that $\delta_k$ is well-defined and positive"), is excluded by the hypothesis $U^k\ne F(U^k)$. The empty product (when $t''_k=t'_k$) is $1$. Components are indexed by `Fin n` (0-based).
-- source:
--   Tsitsiklis, Asynchronous Stochastic Approximation and Q-Learning, Machine Learning 16 (1994), p. 195, §5, Lemma 7 (with the definitions of δ_k and t″_k, pp. 194–195)

import Mathlib
import Definitions.Def_AsyncSA_Monotone_Model

namespace AsyncSA.Monotone

theorem lemma7 {n : ℕ} {Ω : Type*} (alg : Algorithm n Ω) (xstar : Fin n → ℝ) (r : ℝ)
    (h4 : Assumption4 alg.F xstar) (hr : 0 < r) (ω : Ω) (k tk t'k t''k : ℕ)
    (h18 : ∀ t, tk ≤ t →
      Lseq alg.F xstar r k ≤ alg.x t ω ∧ alg.x t ω ≤ Useq alg.F xstar r k)
    (hτ : ∀ t, t'k ≤ t → ∀ i j, tk ≤ alg.τ i j t ω)
    (X : Fin n → ℕ → ℝ)
    (hX0 : ∀ i, X i t'k = Useq alg.F xstar r k i)
    (hX : ∀ i t, t'k ≤ t →
      X i (t + 1) = (1 - alg.α i t ω) * X i t + alg.α i t ω * alg.F (Useq alg.F xstar r k) i)
    (hUF : Useq alg.F xstar r k ≠ alg.F (Useq alg.F xstar r k))
    (δ : ℝ)
    (hδ : IsLeast ((fun i => (Useq alg.F xstar r k i - alg.F (Useq alg.F xstar r k) i) / 4) ''
      {i | 0 < Useq alg.F xstar r k i - alg.F (Useq alg.F xstar r k) i}) δ)
    (ht'' : t'k ≤ t''k)
    (hprod : ∀ i, ∏ s ∈ Finset.Ico t'k t''k, (1 - alg.α i s ω) ≤ 1 / 4)
    (hW : ∀ t, t''k ≤ t → ∀ i,
      tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) t'k t ≤ δ) :
    ∀ i, ∀ t, t''k ≤ t → alg.x t ω i ≤ Useq alg.F xstar r (k + 1) i := by sorry

end AsyncSA.Monotone
