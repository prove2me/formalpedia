-- Prove2me | Theorems.Thm_BayesOrbit_lemma_3_1
-- name    : BayesOrbit.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:18:05.326935+00:00
-- url     : https://prove2.me/theorems/f36f3c6a-146f-4123-a9cb-d332c198aaee
-- title:
--   Lemma 3.1 — closed form of a word in the Bayes operators and their inverses
-- statement:
--   Let $r$ be a signalling structure on finite sets $K$ and $M$, and let $w=((m_1,s_1),\dots,(m_L,s_L))$ be a finite word with $m_l\in M$ and $s_l\in\{\pm1\}$. For $m\in M$ put
--   $$
--   u_m=\#\{l: m_l=m,\ s_l=1\}-\#\{l: m_l=m,\ s_l=-1\}.
--   $$
--   Let $p\in\Delta(K)$ and $q=(\varphi_{m_L}^{s_L}\circ\dots\circ\varphi_{m_1}^{s_1})(p)$. Then:
--
--   1. $p$ and $q$ have the same support;
--   2. for each $k\in K$,
--   $$
--   q[k]=p[k]\,\frac{\prod_m r_k[m]^{u_m}}{\sum_{k'}p[k']\prod_m r_{k'}[m]^{u_m}};\tag{3.1}
--   $$
--   3. for all $k',k''$ in the common support,
--   $$
--   \frac{q[k'']}{q[k']}=\frac{p[k'']}{p[k']}\prod_m\Bigl(\frac{r_{k''}[m]}{r_{k'}[m]}\Bigr)^{u_m}.\tag{3.2}
--   $$
--
--   So the action of a word depends only on its exponent vector, and $q$ has a closed form. This is what turns density of an orbit into a question about the integer combinations $\sum_m u_m\ln r_k[m]$.
--
--   **Formalization Note** The word is a list of pairs, with signs in the units of $\mathbb Z$, and its head $(m_1,s_1)$ is applied first. Powers $r^{u}$ are integer powers.
--
--   Differences from the source:
--   - reading: (3.1) "or, equivalently," (3.2) → both as conjuncts, with the same-support clause; reason: the page asserts both; stating both is the stronger reading
--   - encoding: an integer L with m_1, …, m_L ∈ M and s_1, …, s_L ∈ {±1} → a list w : List (M × ℤˣ), with L its length; reason: Lean convention; same words, the head is applied first
--   - generalization: a signalling structure with at least two signals (§2.2) → SignallingStructure, which also allows one signal; reason: the lemma needs no bound on |M|; the source case is the instances with |M| ≥ 2
-- source:
--   Hellman–Levy, Dense Orbits of the Bayesian Updating Group Action, accepted manuscript (Enlighten 227272), Lemma 3.1, eqs. (3.1), (3.2), pp.7–8

import Mathlib
import Definitions.Def_BayesOrbit_Model

open scoped BigOperators

namespace BayesOrbit

/-- Lemma 3.1 of Hellman–Levy, Dense Orbits of the Bayesian Updating Group Action, accepted
manuscript (Enlighten 227272), pp.7–8 (PDF 8–9), eqs. (3.1), (3.2): for a word
`[(m_1, s_1), …, (m_L, s_L)]` with exponents `u_m` and `q = φ_{m_L}^{s_L} ∘ ⋯ ∘ φ_{m_1}^{s_1}(p)`,
the points `p` and `q` have the same support, (3.1) holds for each `k`, and (3.2) holds for
`k', k''` in the common support.

**Formalization Note.** `s_l ∈ {±1}` is a unit of `ℤ`, `L` is the length of the list, the exponent
`u_m` is an integer power (`zpow`), and `(m_1, s_1)` is applied first (`wordPerm`). -/
theorem lemma_3_1 {K M : Type*} [Fintype K] [Fintype M] [DecidableEq M]
    (S : SignallingStructure K M) (w : List (M × ℤˣ)) (p : stdSimplex ℝ K) :
    Function.support ((S.wordPerm w p : stdSimplex ℝ K) : K → ℝ) =
        Function.support (p : K → ℝ) ∧
    (∀ k : K, ((S.wordPerm w p : stdSimplex ℝ K) : K → ℝ) k =
      (p : K → ℝ) k * ((∏ m, S.r k m ^ wordExponent w m) /
        ∑ k', (p : K → ℝ) k' * ∏ m, S.r k' m ^ wordExponent w m)) ∧
    (∀ k' k'' : K, (p : K → ℝ) k' ≠ 0 → (p : K → ℝ) k'' ≠ 0 →
      ((S.wordPerm w p : stdSimplex ℝ K) : K → ℝ) k'' /
          ((S.wordPerm w p : stdSimplex ℝ K) : K → ℝ) k' =
        (p : K → ℝ) k'' / (p : K → ℝ) k' *
          ∏ m, (S.r k'' m / S.r k' m) ^ wordExponent w m) := by sorry

end BayesOrbit
