-- Prove2me | Theorems.Thm_CompetingChains_Cournot_proposition_6a
-- name    : CompetingChains.Cournot.proposition_6a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:25:39.906125+00:00
-- url     : https://prove2.me/theorems/c2e1b1fb-b5e2-4d21-8b05-e1d29c04c36c
-- title:
--   Proposition 6(a), p. 19 — thresholds k^N_C < k^S_C in (1/2, (3+√5)/4) for the sign of V^N, V^S, decreasing in t and γ_C
-- statement:
--   Under Cournot competition, there exist thresholds $k^S_C$ and $k^N_C$, depending only on the competition intensity $\gamma_C$, the signal accuracy $t$ and the prior variance $\sigma^2$, such that for all $0<\gamma_C<1$, $t>0$, $\sigma^2>0$:
--
--   1. for all $a,c,k$ satisfying the standing assumptions $0<c<a$, $k>a/(4c)$, $k>1/3$,
--   $$
--   V^S_{i,C}>0\iff k<k^S_C,\qquad V^N_{i,C}>0\iff k<k^N_C;
--   $$
--   2. $\tfrac12<k^N_C<k^S_C<\tfrac{3+\sqrt5}{4}$;
--   3. $k^S_C$ and $k^N_C$ are strictly decreasing in $t$ (for fixed $\gamma_C$, $\sigma^2$) and strictly decreasing in $\gamma_C$ on $(0,1)$ (for fixed $t$, $\sigma^2$).
--
--   Here $V^{X_j}_{i,C}=\Pi^{SX_j}_{i,C}-\Pi^{NX_j}_{i,C}$ is the value of information sharing to supply chain $i$. The two thresholds are the boundaries of the three regimes of the information-sharing equilibrium in Proposition 7(a).
--
--   **Formalization Note** The thresholds are functions of $(\gamma_C,t,\sigma^2)$ chosen before $a,c,k$. "Decreasing" is stated as strictly decreasing. The hypothesis $\gamma_C>0$ is added: at $\gamma_C=0$ both thresholds equal $(3+\sqrt5)/4$ and part 2 fails.
-- source:
--   Ha, Tian & Tong, Information Sharing in Competing Supply Chains with Production Cost Reduction (MSOM 2017, pre-published version), p. 19, Proposition 6(a); proof pp. 29–30

import Mathlib
import Definitions.Def_CompetingChains_Cournot_Setting

namespace CompetingChains.Cournot

theorem proposition_6a :
    ∃ kS kN : ℝ → ℝ → ℝ → ℝ,
      (∀ γ t σsq : ℝ, 0 < γ → γ < 1 → 0 < t → 0 < σsq →
        (∀ a c k : ℝ, Standing a c k γ t σsq →
          (0 < V a c k γ t σsq .S ↔ k < kS γ t σsq) ∧
          (0 < V a c k γ t σsq .N ↔ k < kN γ t σsq)) ∧
        1 / 2 < kN γ t σsq ∧ kN γ t σsq < kS γ t σsq ∧
        kS γ t σsq < (3 + Real.sqrt 5) / 4) ∧
      (∀ γ σsq : ℝ, 0 < γ → γ < 1 → 0 < σsq →
        StrictAntiOn (fun t => kS γ t σsq) (Set.Ioi 0) ∧
        StrictAntiOn (fun t => kN γ t σsq) (Set.Ioi 0)) ∧
      (∀ t σsq : ℝ, 0 < t → 0 < σsq →
        StrictAntiOn (fun γ => kS γ t σsq) (Set.Ioo 0 1) ∧
        StrictAntiOn (fun γ => kN γ t σsq) (Set.Ioo 0 1)) := by sorry

end CompetingChains.Cournot
