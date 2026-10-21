-- Prove2me | Theorems.Thm_DynOpaque_TwoPeriod_lemma_1
-- name    : DynOpaque.TwoPeriod.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:19.121635+00:00
-- url     : https://prove2.me/theorems/5309f612-dcec-43e2-b050-d79c868ab0a6
-- title:
--   Lemma 1 (K = 1), p. 10 — purchasing fractions at vL and vHL; every opaque price pair is dominated by a pair in {vL, vHL}
-- statement:
--   Assume the standing assumptions $v_H>v_L$, $c_H>c_L$, $0\le\alpha\le1$, $c_L\le v_L$, and let $\xi_1,\xi_2\in[0,1]$. With one anecdote per customer, the candidate prices of Lemma 1 are $p^{(0)}=v_L$ and $p^{(1)}=v_{HL}=\frac{v_H-v_L}{2}+v_L$. Then:
--
--   1. The purchasing fractions at the candidate prices are
--   $$
--   \gamma_1(v_{HL},\xi_1)=\xi_1,\quad \gamma_1(v_L,\xi_1)=1,\quad \gamma_2(v_{HL},\xi_2,\xi_1)=\alpha\xi_1+(1-\alpha)\xi_2,\quad \gamma_2(v_L,\xi_2,\xi_1)=1 .
--   $$
--   2. For all prices $p_1,p_2\le v_{HL}$ there are $p_1',p_2'\in\{v_L,v_{HL}\}$ with
--   $$
--   \Pi(\xi_1,\xi_2\mid p_1,p_2)\le\Pi(\xi_1,\xi_2\mid p_1',p_2').
--   $$
--
--   This is the $K=1$ instance of Lemma 1: only two prices need to be considered, and at each the demand is an explicit linear function of the offering probabilities. It reduces the firm's pricing problem to the four price pairs analysed in §4.
--
--   **Formalization Note** Lemma 1 is stated for general $K$ with binomial sums; only $K=1$ is formalized. "The optimal price lies in the candidate set" is stated as weak domination by a candidate pair with the same $\xi$. Opaque prices are at most $v_{HL}$ by the model's feasibility convention.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927, p. 10, Lemma 1 (instance K = 1)

import Mathlib
import Definitions.Def_DynOpaque_TwoPeriod_Model

namespace DynOpaque.TwoPeriod

/-- Lemma 1, p. 10, in its `K = 1` instance: the purchasing fractions at the two candidate
prices `vL = p^(0)` and `vHL = p^(1)`, and every feasible opaque price pair is weakly dominated by a
candidate price pair with the same offering probabilities. -/
theorem lemma_1 (vH vL cH cL α ξ₁ ξ₂ : ℝ) (hS : Standing vH vL cH cL α)
    (hξ₁ : ξ₁ ∈ Set.Icc (0 : ℝ) 1) (hξ₂ : ξ₂ ∈ Set.Icc (0 : ℝ) 1) :
    (frac vH vL ξ₁ (vHL vH vL) = ξ₁ ∧ frac vH vL ξ₁ vL = 1 ∧
      frac vH vL (α * ξ₁ + (1 - α) * ξ₂) (vHL vH vL) = α * ξ₁ + (1 - α) * ξ₂ ∧
      frac vH vL (α * ξ₁ + (1 - α) * ξ₂) vL = 1) ∧
    ∀ p₁ p₂ : ℝ, p₁ ≤ vHL vH vL → p₂ ≤ vHL vH vL →
      ∃ p₁' ∈ ({vL, vHL vH vL} : Set ℝ), ∃ p₂' ∈ ({vL, vHL vH vL} : Set ℝ),
        opaqueProfit vH vL cH cL α p₁ p₂ ξ₁ ξ₂ ≤ opaqueProfit vH vL cH cL α p₁' p₂' ξ₁ ξ₂ := by sorry

end DynOpaque.TwoPeriod
