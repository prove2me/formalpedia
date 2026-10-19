-- Prove2me | Theorems.Thm_DynOpaque_TwoPeriod_lemma_4_corrected
-- name    : DynOpaque.TwoPeriod.lemma_4_corrected
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:19.496248+00:00
-- url     : https://prove2.me/theorems/d7b22c13-668b-496d-b0d2-25811f3bcded
-- title:
--   Lemma 4 (corrected), p. 12 — at p1 = vL, p2 = vHL some optimum has ξ1 ∈ {0, 1}, dominated by (3) or (4)
-- statement:
--   Assume $v_H>v_L$, $c_H>c_L$, $0\le\alpha\le1$, $c_L\le v_L$, and consider objective (5), the profit at $p_1=v_L$, $p_2=v_{HL}$, together with objectives (3) and (4). This is a **corrected** version of Lemma 4:
--
--   1. (i′) for every $(\xi_1,\xi_2)\in[0,1]^2$ there is $(\xi_1',\xi_2')\in[0,1]^2$ with $\xi_1'\in\{0,1\}$ and
--   $$
--   \Pi(\xi_1,\xi_2\mid v_L,v_{HL})\le\Pi(\xi_1',\xi_2'\mid v_L,v_{HL});
--   $$
--   2. (ii) for every $\xi_2\in[0,1]$, $\Pi(1,\xi_2\mid v_L,v_{HL})\le\Pi(1,\xi_2\mid v_{HL},v_{HL})$;
--   3. (iii) for every $\xi_2\in[0,1]$ there is $(\xi_1',\xi_2')\in[0,1]^2$ with $\Pi(0,\xi_2\mid v_L,v_{HL})\le\Pi(\xi_1',\xi_2'\mid v_{HL},v_L)$.
--
--   Together, the price pair $(v_L,v_{HL})$ is never needed: its best value is matched by $(v_{HL},v_{HL})$ or by $(v_{HL},v_L)$.
--
--   **Formalization Note** Part (i) as printed, "$\xi_1=1$ or $\xi_2=0$ is optimal", is false: at $\alpha=0$, $c_L=0$, $c_H=1$, $v_L=1$, $v_H=3/2$, objective (5) equals $1-\xi_1+\xi_2(5/4-\xi_2)$, whose maximum $89/64$ over $[0,1]^2$ is attained only at $(0,5/8)$. Parts (ii) and (iii) of the page treat exactly the cases $\xi_1=1$ and $\xi_1=0$, which shows the intended claim: (5) is affine in $\xi_1$, so some optimum has $\xi_1\in\{0,1\}$. Part (i′) states that claim; (ii) and (iii) are as printed, with "dominated" read as a weak inequality against some decision of the other case.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927, p. 12, Lemma 4 (part (i) corrected)

import Mathlib
import Definitions.Def_DynOpaque_TwoPeriod_Model

namespace DynOpaque.TwoPeriod

/-- Lemma 4, p. 12, CORRECTED (`p₁ = vL`, `p₂ = vHL`, objective (5)). Part (i) as printed
("ξ₁ = 1 or ξ₂ = 0 is optimal") is false; the corrected (i′) says that some optimal decision has
`ξ₁ ∈ {0, 1}`, in the form: every offering pair is weakly beaten by one with `ξ₁ ∈ {0, 1}`.
(ii) with `ξ₁ = 1`, (5) is dominated by (3); (iii) with `ξ₁ = 0`, (5) is dominated by (4). -/
theorem lemma_4_corrected (vH vL cH cL α : ℝ) (hS : Standing vH vL cH cL α) :
    (∀ x ∈ box, ∃ y ∈ box, (y.1 = 0 ∨ y.1 = 1) ∧
      obj5 vH vL cH cL α x.1 x.2 ≤ obj5 vH vL cH cL α y.1 y.2) ∧
    (∀ ξ₂ ∈ Set.Icc (0 : ℝ) 1, obj5 vH vL cH cL α 1 ξ₂ ≤ obj3 vH vL cH cL α 1 ξ₂) ∧
    (∀ ξ₂ ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ box, obj5 vH vL cH cL α 0 ξ₂ ≤ obj4 vH vL cH cL y.1 y.2) := by sorry

end DynOpaque.TwoPeriod
