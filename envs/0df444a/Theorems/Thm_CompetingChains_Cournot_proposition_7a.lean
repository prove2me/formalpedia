-- Prove2me | Theorems.Thm_CompetingChains_Cournot_proposition_7a
-- name    : CompetingChains.Cournot.proposition_7a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:25:59.284614+00:00
-- url     : https://prove2.me/theorems/871c2d55-e982-4841-9c7f-50b87c76515b
-- title:
--   Proposition 7(a), p. 21 — Cournot: (S,S) unique below k_N, (S,S) and (N,N) with (S,S) Pareto-better between, (N,N) unique above k_S
-- statement:
--   Fix the competition intensity $0<\gamma_C<1$, the signal accuracy $t>0$ and the prior variance $\sigma^2>0$. There exist thresholds $k^N_C<k^S_C$ with
--
--   $$
--   \tfrac12<k^N_C<k^S_C<\tfrac{3+\sqrt5}{4}
--   $$
--
--   such that, for all $a,c,k$ satisfying the standing assumptions $0<c<a$, $k>a/(4c)$, $k>1/3$, the set $\mathcal E$ of pure-strategy equilibria of the stage-one information-sharing game between the two manufacturers (Table 1) is:
--
--   1. if $k<k^N_C$: $\mathcal E=\{(S,S)\}$;
--   2. if $k^N_C<k<k^S_C$: $\mathcal E=\{(S,S),(N,N)\}$, and each manufacturer's payoff at $(S,S)$ is strictly larger than at $(N,N)$;
--   3. if $k>k^S_C$: $\mathcal E=\{(N,N)\}$.
--
--   Here manufacturer $i$ chooses whether chain $i$ shares ($S$) or not ($N$), pays the retailer the side payment $\hat m$ needed to induce sharing, and earns $\Pi^{SX_j}_{M_i,C}-\hat m^{X_j}$ if it shares and $\Pi^{NX_j}_{M_i,C}$ otherwise.
--
--   This is the main result of the Cournot half of the paper: information sharing is the unique outcome when cost reduction is efficient, a coordination problem with a Pareto-better sharing equilibrium at intermediate efficiency, and absent when cost reduction is inefficient.
--
--   **Formalization Note** The thresholds depend only on $(\gamma_C,t,\sigma^2)$ and are chosen before $a,c,k$; their bounds are those of Proposition 6(a)(2), and they make all three cases nonempty. The page's "otherwise" is stated as $k>k^S_C$: at $k=k^N_C$ and $k=k^S_C$ both $(S,S)$ and $(N,N)$ are equilibria, so the boundary points are left out. Only pure-strategy equilibria are counted, as in the paper (the middle region also has a mixed equilibrium). "Pareto optimal" is the strict inequality of the payoffs at $(S,S)$ over $(N,N)$, stated for manufacturer 1; by symmetry it is the same for manufacturer 2. The hypothesis $\gamma_C>0$ is added (at $\gamma_C=0$ the middle region is empty).
-- source:
--   Ha, Tian & Tong, Information Sharing in Competing Supply Chains with Production Cost Reduction (MSOM 2017, pre-published version), p. 21, Proposition 7(a); proof p. 31

import Mathlib
import Definitions.Def_CompetingChains_Cournot_Setting

namespace CompetingChains.Cournot

theorem proposition_7a (γ t σsq : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (ht : 0 < t) (hσ : 0 < σsq) :
    ∃ kN kS : ℝ, 1 / 2 < kN ∧ kN < kS ∧ kS < (3 + Real.sqrt 5) / 4 ∧
      ∀ a c k : ℝ, Standing a c k γ t σsq →
        (k < kN → equilibria a c k γ t σsq = {(.S, .S)}) ∧
        (kN < k → k < kS →
          equilibria a c k γ t σsq = {(.S, .S), (.N, .N)} ∧
            payoff a c k γ t σsq .N .N < payoff a c k γ t σsq .S .S) ∧
        (kS < k → equilibria a c k γ t σsq = {(.N, .N)}) := by sorry

end CompetingChains.Cournot
