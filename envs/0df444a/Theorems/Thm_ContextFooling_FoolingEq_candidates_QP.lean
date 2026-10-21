-- Prove2me | Theorems.Thm_ContextFooling_FoolingEq_candidates_QP
-- name    : ContextFooling.FoolingEq.candidates_QP
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:53.001635+00:00
-- url     : https://prove2.me/theorems/74add452-bfe8-4f26-a4ad-cbae162a4625
-- title:
--   Proof of Prop. 2, p. 44 (PDF 45), (Q*) and (P*) — the zero-profit store-wide candidates, with q_a = q^P + β[b − c(q^P)]
-- statement:
--   Under the standing assumptions, the two store-wide profit bounds vanish exactly at the switching surpluses:
--
--   $$\beta q^Q-c(q^Q)-(\beta-1)\underline q-\bar u=0\iff \bar u=\nu^{(Q,Q)},\qquad \frac{q^P-\beta c(q^P)+(\beta-1)b-\bar u}{\beta}=0\iff\bar u=\nu^{(P,P)}.$$
--
--   At these values the maximizers are the candidates
--
--   - (Q\*): $\theta=Q$, $(q_t,p_t)=(q^Q,c(q^Q))$, $(q_a,p_a)=(\underline q,\ c(q^Q)-\beta(q^Q-\underline q))$;
--   - (P\*): $\theta=P$, $(q_t,p_t)=(q^P,c(q^P))$, $(q_a,p_a)=(q^P+\beta[b-c(q^P)],\ b)$.
--
--   In each candidate:
--   1. both products are acceptable;
--   2. the pair fools every type $\tilde\beta\in(1,\beta)$;
--   3. the attraction product gives $u_a=\nu$;
--   4. the target sells at cost;
--   5. the attraction product is priced below its cost, $p_a<c(q_a)$.
--
--   These are the menus that firms with positive demand offer in the store-wide equilibrium of Proposition 2.
--
--   **Formalization Note.** The paper prints (P\*) as $q_a=q^P+[b-c(q^P)]$, without the factor $\beta$. Proposition 2 itself (p. 16), and $q_a=b+\bar u$ at $\bar u=\nu^{(P,P)}$, both give $q^P+\beta[b-c(q^P)]$, which is the value stated here.
-- source:
--   Apffelstaedt & Mechtenberg, Competition for Context-Sensitive Consumers, MPRA Paper No. 99509 (version of November 2016; published in Management Science, doi:10.1287/mnsc.2020.3675), p. 44 (PDF 45), proof of Proposition 2, displays (Q*) and (P*)

import Mathlib
import Definitions.Def_ContextFooling_FoolingEq_Model

namespace ContextFooling.FoolingEq

/-- Proof of Proposition 2, p. 44, displays (Q*) and (P*): the store-wide best-response profit
bounds vanish exactly at ū = ν^(Q,Q) and ū = ν^(P,P); there the maximizers are (Q*) and (P*)
(the latter with q_a = q^P + β[b − c(q^P)]), which are acceptable, fool every type
β̃ ∈ (1, β), give the attraction surplus ν, sell the target at cost, and price the attraction
product below its cost. -/
theorem candidates_QP (P : Params) (hP : P.Standing) :
    (∀ ubar : ℝ, P.β * P.qQ - P.c P.qQ - (P.β - 1) * P.qlow - ubar = 0 ↔ ubar = nuQQ P) ∧
    (⟨P.qQ, P.β * (P.qQ - P.qlow) + P.qlow - nuQQ P, Ctx.Q⟩ : Product) = tQ P ∧
    (⟨P.qlow, P.qlow - nuQQ P, Ctx.Q⟩ : Product) = aQ P ∧
    Acceptable P (aQ P) ∧ Acceptable P (tQ P) ∧
    (∀ γ ∈ Set.Ioo 1 P.β, Fools P.β γ (aQ P) (tQ P)) ∧
    u (aQ P) = nuQQ P ∧ (tQ P).p = P.c (tQ P).q ∧ (aQ P).p < P.c (aQ P).q ∧
    (∀ ubar : ℝ, (P.qP - P.β * P.c P.qP + (P.β - 1) * P.b - ubar) / P.β = 0 ↔ ubar = nuPP P) ∧
    (⟨P.qP, P.b - (P.b + nuPP P - P.qP) / P.β, Ctx.P⟩ : Product) = tP P ∧
    (⟨P.b + nuPP P, P.b, Ctx.P⟩ : Product) = aP P ∧
    Acceptable P (aP P) ∧ Acceptable P (tP P) ∧
    (∀ γ ∈ Set.Ioo 1 P.β, Fools P.β γ (aP P) (tP P)) ∧
    u (aP P) = nuPP P ∧ (tP P).p = P.c (tP P).q ∧ (aP P).p < P.c (aP P).q := by sorry

end ContextFooling.FoolingEq
