-- Prove2me | Theorems.Thm_ContextFooling_FoolingEq_candidate_PQ
-- name    : ContextFooling.FoolingEq.candidate_PQ
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:44.002016+00:00
-- url     : https://prove2.me/theorems/702ad1df-95bd-4670-a851-0421b81f066d
-- title:
--   Proof of Prop. 2, p. 47 (PDF 48), (PQ*) — the zero-profit product-specific candidate
-- statement:
--   Under the standing assumptions, the product-specific profit bound $\nu^{(P,Q)}-\bar u$ vanishes exactly at $\bar u=\nu^{(P,Q)}$. There the maximizer is the candidate
--
--   $$\text{(PQ*)}\qquad (\theta_a,\theta_t)=(P,Q),\quad (q_t,p_t)=(q^Q,c(q^Q)),\quad (q_a,p_a)=\bigl(\beta(q^Q+b)-c(q^Q),\ b\bigr).$$
--
--   In this candidate:
--   1. both products are acceptable;
--   2. the pair fools every type $\tilde\beta\in(1,\beta)$;
--   3. the attraction product gives $u_a=\nu^{(P,Q)}$;
--   4. the target sells at cost;
--   5. the attraction product is priced below its cost, $p_a<c(q_a)$.
--
--   This is the menu that firms with positive demand offer in the product-specific equilibrium of Proposition 2.
-- source:
--   Apffelstaedt & Mechtenberg, Competition for Context-Sensitive Consumers, MPRA Paper No. 99509 (version of November 2016; published in Management Science, doi:10.1287/mnsc.2020.3675), p. 47 (PDF 48), proof of Proposition 2, display (PQ*)

import Mathlib
import Definitions.Def_ContextFooling_FoolingEq_Model

namespace ContextFooling.FoolingEq

/-- Proof of Proposition 2, p. 47, display (PQ*): the product-specific profit bound vanishes
exactly at ū = ν^(P,Q); there the maximizer is (PQ*), which is acceptable, fools every type
β̃ ∈ (1, β), gives the attraction surplus ν^(P,Q), sells the target at cost, and prices the
attraction product below its cost. -/
theorem candidate_PQ (P : Params) (hP : P.Standing) :
    (∀ ubar : ℝ, nuPQ P - ubar = 0 ↔ ubar = nuPQ P) ∧
    (⟨P.qQ, P.β * P.qQ - nuPQ P + (P.β - 1) * P.b, Ctx.Q⟩ : Product) = tPQ P ∧
    (⟨P.b + nuPQ P, P.b, Ctx.P⟩ : Product) = aPQ P ∧
    Acceptable P (aPQ P) ∧ Acceptable P (tPQ P) ∧
    (∀ γ ∈ Set.Ioo 1 P.β, Fools P.β γ (aPQ P) (tPQ P)) ∧
    u (aPQ P) = nuPQ P ∧ (tPQ P).p = P.c (tPQ P).q ∧ (aPQ P).p < P.c (aPQ P).q := by sorry

end ContextFooling.FoolingEq
