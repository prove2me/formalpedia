-- Prove2me | Theorems.Thm_ContextFooling_FoolingEq_proposition_2
-- name    : ContextFooling.FoolingEq.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:52.700905+00:00
-- url     : https://prove2.me/theorems/cb7857d6-cb3b-4810-a6a5-26e35f5f12ce
-- title:
--   Proposition 2, pp. 15–16 (PDF 16–17) — fooling equilibrium: two products t ≠ a; up-sell iff ν^(Q,Q) > ν^(P,P) (store-wide); down-sell with (P,Q) (product-specific)
-- statement:
--   **Proposition 2 (Fooling Equilibrium).** Assume the standing assumptions. Assume also that consumers underestimate their sensitivity to context: almost every type satisfies $\tilde\beta<\beta$.
--
--   **a) Store-wide distortions.** Each store gives all its products one context $\theta^k\in\{Q,P,N\}$.
--   1. A competitive equilibrium exists.
--   2. In every competitive equilibrium, at least two firms have positive demand, and every other firm offers the empty menu.
--   3. Each firm with positive demand offers exactly two products: a target $t$, which entrants buy, and an attraction product $a\ne t$, which every type $\tilde\beta\in(1,\beta)$ expects to buy. These are:
--      - if $\nu^{(Q,Q)}>\nu^{(P,P)}$, the menu (Q\*): context $Q$, $t=(q^Q,c(q^Q))$, $a=(\underline q,\ c(q^Q)-\beta(q^Q-\underline q))$. The firm up-sells.
--      - if $\nu^{(Q,Q)}<\nu^{(P,P)}$, the menu (P\*): context $P$, $t=(q^P,c(q^P))$, $a=(q^P+\beta[b-c(q^P)],\ b)$. The firm down-sells.
--      - if $\nu^{(Q,Q)}=\nu^{(P,P)}$, one of the two menus above.
--
--   Here
--
--   $$\nu^{(Q,Q)}=[q^Q-c(q^Q)]+(\beta-1)(q^Q-\underline q),\qquad \nu^{(P,P)}=[q^P-c(q^P)]+(\beta-1)[b-c(q^P)].$$
--
--   **b) Product-specific distortions.** Each product gets its own context.
--   1. A competitive equilibrium exists.
--   2. In every competitive equilibrium, at least two firms have positive demand and the others offer the empty menu.
--   3. Each firm with positive demand offers the menu (PQ\*): $\theta_a=P$, $\theta_t=Q$, $t=(q^Q,c(q^Q))$, $a=(\beta(q^Q+b)-c(q^Q),\ b)$. The firm down-sells.
--
--   **Comparisons.** Moreover:
--   1. $q^Q>q^*>q^P$;
--   2. in (Q\*): $q_a<q_t$, $p_a<p_t$, $p_a<c(q_a)$;
--   3. in (P\*): $q_t<q_a$, $p_t<p_a$, $p_a<c(q_a)$;
--   4. in (PQ\*): $q_t<q_a$, $p_a<c(q_a)$, $p_t\le p_a$, and $p_t<p_a$ when $c(q^Q)<b$.
--
--   In every case the attraction product is a loss leader, and the target is sold at marginal cost.
--
--   **Formalization Note.**
--   1. Competitive equilibrium, demand and the context technologies are those of the model file.
--   2. "At least 2 firms share the market" is "at least two firms have positive demand".
--   3. "Attracts with $a$" is "every type in $(1,\beta)$ predicts exactly $a$"; "sells $t$" is "$t$ is bought and strictly more profitable than any other bought product".
--   4. In the equal-$\nu$ case the choice between (Q\*) and (P\*) is made firm by firm.
--   5. Part b)'s printed "$p_a=b>p_t$" fails at the admissible boundary $b=c(q^Q)$, where $p_t=c(q^Q)=b$. The statement asserts $p_t\le p_a$, and the strict inequality when $c(q^Q)<b$.
-- source:
--   Apffelstaedt & Mechtenberg, Competition for Context-Sensitive Consumers, MPRA Paper No. 99509 (version of November 2016; published in Management Science, doi:10.1287/mnsc.2020.3675), pp. 15–16 (PDF 16–17), Proposition 2

import Mathlib
import Definitions.Def_ContextFooling_FoolingEq_Model

namespace ContextFooling.FoolingEq

/-- Proposition 2 (Fooling Equilibrium), pp. 15–16, for optimistic types (β̃ < β a.s.). -/
theorem proposition_2 (P : Params) (hP : P.Standing) (hopt : P.μ (Set.Iio P.β)ᶜ = 0) :
    -- a) store-wide distortions
    (∃ σ : Profile P, IsCompEq P StoreWide σ) ∧
    (∀ σ : Profile P, IsCompEq P StoreWide σ →
      2 ≤ (active P σ).card ∧ (∀ k, ¬ PosDemand P σ k → σ k = ∅) ∧
      ∀ k, PosDemand P σ k →
        (nuPP P < nuQQ P → Roles P (σ k) (tQ P) (aQ P)) ∧
        (nuQQ P < nuPP P → Roles P (σ k) (tP P) (aP P)) ∧
        (nuQQ P = nuPP P → Roles P (σ k) (tQ P) (aQ P) ∨ Roles P (σ k) (tP P) (aP P))) ∧
    -- b) product-specific distortions
    (∃ σ : Profile P, IsCompEq P ProductSpecific σ) ∧
    (∀ σ : Profile P, IsCompEq P ProductSpecific σ →
      2 ≤ (active P σ).card ∧ (∀ k, ¬ PosDemand P σ k → σ k = ∅) ∧
      ∀ k, PosDemand P σ k → Roles P (σ k) (tPQ P) (aPQ P)) ∧
    -- the comparisons the proposition states about these products
    P.qS < P.qQ ∧ P.qP < P.qS ∧
    (aQ P).q < (tQ P).q ∧ (aQ P).p < (tQ P).p ∧ (aQ P).p < P.c (aQ P).q ∧
    (tP P).q < (aP P).q ∧ (tP P).p < (aP P).p ∧ (aP P).p < P.c (aP P).q ∧
    (tPQ P).q < (aPQ P).q ∧ (tPQ P).p ≤ (aPQ P).p ∧ (P.c P.qQ < P.b → (tPQ P).p < (aPQ P).p) ∧
    (aPQ P).p < P.c (aPQ P).q := by sorry

end ContextFooling.FoolingEq
