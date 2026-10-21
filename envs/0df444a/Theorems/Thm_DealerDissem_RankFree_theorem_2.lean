-- Prove2me | Theorems.Thm_DealerDissem_RankFree_theorem_2
-- name    : DealerDissem.RankFree.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:26.333134+00:00
-- url     : https://prove2.me/theorems/557e98ad-1a0a-48cf-8e37-48ccf61858d7
-- title:
--   Theorem 2, p. 15 — the strategies built from $\Omega$ and a selection $T$ of the targets form a rank-free equilibrium with payoff $r\Omega(y)$
-- statement:
--   Throughout, $\rho>0$ is the sure return of the asset, $r>0$ the funding spread, $q\in(0,1)$ the probability that a dealer is available, and $G$ the distribution of the customer demand $\tilde\omega$, a probability distribution on $\mathbb R_+$ with finite mean; $H(\omega)=\Pr(\tilde\omega\ge\omega)$. Let $\Omega:\mathbb R_+\to\mathbb R$ be bounded, continuous and a solution of the functional equation (9), $$\Omega(0)=0,\qquad \Omega(y)=\sup_{0\le\omega\le y} qH(\omega)\bigl(\omega+\Omega(y-\omega)\bigr)\quad (y>0).$$
--
--   By Theorem 1 this is the collected demand. Choose a selection $T$ of the targeted values, $T(y)\in\mathcal T(y)$ for every $y\ge0$. For a dealer receiving an offer $(p,v)$, with customer demand $\omega$ and financing needs $y=\max(pv-\omega,0)$, write
--   $$\pi^*(p,v,y)=(\rho-p)v-ry+r\Omega(y).$$
--   Consider the strategies: accept iff $\pi^*(p,v,y)\ge0$; on acceptance make the offer $(P(y),V(y))$ characterized by
--   $$P(y)V(y)=y\quad\text{and}\quad(\rho-P(y))V(y)-ry+r\bigl(T(y)+\Omega(y-T(y))\bigr)=0.\tag{14}$$
--   Then:
--
--   1. these strategies form a **rank-free equilibrium** (Definition 1): after acceptance the offer is feasible and maximizes the expected profit (5) over all feasible offers, with acceptance probabilities computed from the same rule, and a dealer accepts iff some feasible offer gives her a non-negative profit;
--   2. for $p>\rho$ (and $v>0$) the offer is rejected;
--   3. for an accepted offer with $y=0$: no further offer is made ($V(0)=0$) and the profit is $\pi^*(p,v,0)=(\rho-p)v$;
--   4. for an accepted offer with $y>0$: $(P(y),V(y))$ satisfies (14), $P(y)\le\rho$, $0\le V(y)\le v-\omega/\rho$, the expected transaction payoff equals $r\Omega(y)$, and the dealer's profit equals $\pi^*(p,v,y)$.
--
--   This is the paper's main result: it constructs an equilibrium of the dealer-chain game from the collected demand, which the paper then uses to study how far an asset disseminates.
--
--   **Formalization Note.** Definition 1 (ii) is encoded as: (a) after acceptance, the strategy's offer is feasible and maximizes (5) over every feasible offer; (b) acceptance holds iff some feasible offer has non-negative profit. The acceptance probability inside (5) is the $G$-measure of the acceptance set of the rule under test, never a free parameter; the equilibrium predicate requires measurable acceptance events for feasible offers. The equilibrium offer depends on $(p,v,\omega)$ only through $y$, and $V$ is (14) solved for $V$ (the paper's (16)); $P(0)$ is Lean's junk $0/0=0$, harmless since $V(0)=0$. Two hypotheses are added where the printed statement is false without them: $v>0$ on "this case surely occurs for $p>\rho$" (at $v=0$, $\pi^*=0$ and the offer is accepted), and $y>0$ on the bound $0\le V(y)\le v-\omega/\rho$ (the theorem's own case "For $y>0$"). $\Omega$ enters through hypotheses (bounded, continuous on $\mathbb R_+$, solves (9)), which by Theorem 1 characterize the collected demand.
-- source:
--   Colliard & Demange, Asset Dissemination through Dealer Markets, SSRN 3244321 (authors' version of September 17, 2020), p. 15 (PDF 17), Theorem 2; proof pp. 42–44 (PDF 44–46)

import Mathlib
import Definitions.Def_DealerDissem_RankFree_Model

open MeasureTheory

namespace DealerDissem.RankFree

/-- Theorem 2, p. 15: for `Ω` the collected demand and any selection `T` of `𝒯`, the strategies
"accept iff `π*(p, v, y) ≥ 0`; on acceptance offer `(P(y), V(y))` from (14)" form a rank-free
equilibrium, with the properties listed in the theorem. -/
theorem theorem_2 (P : Params) (μ : Measure ℝ) (hμ : IsDemandDist μ)
    (Ω : ℝ → ℝ) (hΩb : BoundedOnNonneg Ω) (hΩc : ContinuousOn Ω (Set.Ici 0))
    (hΩ : SolvesCollected P μ Ω) (T : ℝ → ℝ) (hT : IsSelection P μ Ω T) :
    IsRankFreeEquilibrium P μ (thmAccept P Ω)
        (fun p v ω => offerP P Ω T (finNeeds p v ω))
        (fun p v ω => offerV P Ω T (finNeeds p v ω)) ∧
    (∀ p v ω, 0 ≤ ω → 0 < v → P.ρ < p → ¬ thmAccept P Ω p v ω) ∧
    (∀ p v ω, 0 ≤ p → 0 ≤ v → 0 ≤ ω → thmAccept P Ω p v ω → finNeeds p v ω = 0 →
        offerV P Ω T 0 = 0 ∧ piStar P Ω p v 0 = (P.ρ - p) * v ∧
        profit P μ (thmAccept P Ω) p v ω (offerP P Ω T 0) (offerV P Ω T 0) = (P.ρ - p) * v) ∧
    (∀ p v ω, 0 ≤ p → 0 ≤ v → 0 ≤ ω → thmAccept P Ω p v ω → 0 < finNeeds p v ω →
        offerP P Ω T (finNeeds p v ω) * offerV P Ω T (finNeeds p v ω) = finNeeds p v ω ∧
        (P.ρ - offerP P Ω T (finNeeds p v ω)) * offerV P Ω T (finNeeds p v ω)
            - P.r * finNeeds p v ω
            + P.r * (T (finNeeds p v ω) + Ω (finNeeds p v ω - T (finNeeds p v ω))) = 0 ∧
        offerP P Ω T (finNeeds p v ω) ≤ P.ρ ∧
        0 ≤ offerV P Ω T (finNeeds p v ω) ∧
        offerV P Ω T (finNeeds p v ω) ≤ v - ω / P.ρ ∧
        P.q * accProb μ (thmAccept P Ω) (offerP P Ω T (finNeeds p v ω))
              (offerV P Ω T (finNeeds p v ω)) *
            (P.r * min (offerP P Ω T (finNeeds p v ω) * offerV P Ω T (finNeeds p v ω))
                (finNeeds p v ω)
              - (P.ρ - offerP P Ω T (finNeeds p v ω)) * offerV P Ω T (finNeeds p v ω))
          = P.r * Ω (finNeeds p v ω) ∧
        profit P μ (thmAccept P Ω) p v ω (offerP P Ω T (finNeeds p v ω))
            (offerV P Ω T (finNeeds p v ω))
          = piStar P Ω p v (finNeeds p v ω)) := by sorry

end DealerDissem.RankFree
