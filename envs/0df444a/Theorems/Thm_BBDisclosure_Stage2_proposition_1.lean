-- Prove2me | Theorems.Thm_BBDisclosure_Stage2_proposition_1
-- name    : BBDisclosure.Stage2.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:50.444993+00:00
-- url     : https://prove2.me/theorems/31afe13d-2425-475d-8688-2ea595b6bbc3
-- title:
--   Proposition 1 (a)–(c), p. 8519 — under BBD, q̂*_io < q̂*_in, p*_in < p*_io, and BBD raises second-period profits relative to uniform disclosure
-- statement:
--   Consider the second period of the Hotelling duopoly at the symmetric first-period share $x_1=1/2$, with unit disclosure cost $0<c<5/36$. Then:
--   1. a second-period equilibrium exists under behavior-based disclosure (BBD), and one exists under uniform disclosure;
--   2. (part (a)) in every BBD equilibrium, each firm's disclosure threshold for its own customers is strictly below its threshold for the competitor's customers:
--   $$\hat q_{ao}<\hat q_{an}\qquad\text{and}\qquad \hat q_{bo}<\hat q_{bn};$$
--   3. (part (b)) in every BBD equilibrium and for every realization $(q_a,q_b)\in[0,1]^2$, each firm's price to the competitor's customers is strictly below its price to its own customers, at the equilibrium beliefs $\tilde q_{ik}=\operatorname{bel}(\hat q_{ik},q_i)$:
--   $$p_{an}<p_{ao}\qquad\text{and}\qquad p_{bn}<p_{bo};$$
--   4. (part (c)) for every BBD equilibrium and every uniform-disclosure equilibrium, each firm's ex ante second-period profit is strictly higher under BBD:
--   $$E(\pi_{a2})^{\mathrm U}<E(\pi_{a2})^{\mathrm{BBD}}\qquad\text{and}\qquad E(\pi_{b2})^{\mathrm U}<E(\pi_{b2})^{\mathrm{BBD}}.$$
--
--   Part (a) says that disclosure is retention focused: a firm discloses quality to its own customers over a wider range of qualities than to its rival's. Part (b) says that pricing, by contrast, is acquisition focused: the rival's customers get the discount. Part (c) says that, in contrast with behavior-based pricing alone, letting firms target disclosure by purchase history raises their second-period profits.
--
--   **Formalization Note** $x_1=1/2$ is the symmetric first-period equilibrium share (Table 1; (7), (9), (16), (17)), which is the subject of the companion mission. Part (b) is stated realization by realization: $p_{ao},p_{bn}$ are the components of A's-turf price strategy at the beliefs $(\operatorname{bel}(\hat q_{ao},q_a),\operatorname{bel}(\hat q_{bn},q_b))$ of A's old customers, and $p_{an},p_{bo}$ those of B's-turf strategy at $(\operatorname{bel}(\hat q_{an},q_a),\operatorname{bel}(\hat q_{bo},q_b))$; both beliefs about a firm come from the same realized quality. The existence clauses make the universal clauses non-vacuous. "Firms'" is stated for both firms rather than for A with symmetry assumed. $c>0$ is needed for the strict inequality in (c), whose two sides coincide at $c=0$.
-- source:
--   Zhang and Li, Retention or Acquisition? Behavior-Based Quality Disclosure, Management Sci. 71(10) (2025) 8510–8525, DOI 10.1287/mnsc.2022.01081, p. 8519, Proposition 1 (a)–(c)

import Mathlib
import Definitions.Def_BBDisclosure_Stage2_Model

namespace BBDisclosure.Stage2

theorem proposition_1 (c : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36) :
    (∃ e : ProfileBBD, IsStage2EqBBD c (1 / 2) e) ∧
    (∃ u : ProfileU, IsStage2EqU c (1 / 2) u) ∧
    (∀ e : ProfileBBD, IsStage2EqBBD c (1 / 2) e → e.qao < e.qan ∧ e.qbo < e.qbn) ∧
    (∀ e : ProfileBBD, IsStage2EqBBD c (1 / 2) e →
      ∀ qa ∈ Set.Icc (0 : ℝ) 1, ∀ qb ∈ Set.Icc (0 : ℝ) 1,
        (e.σB (bel e.qan qa) (bel e.qbo qb)).1 < (e.σA (bel e.qao qa) (bel e.qbn qb)).1 ∧
          (e.σA (bel e.qao qa) (bel e.qbn qb)).2 < (e.σB (bel e.qan qa) (bel e.qbo qb)).2) ∧
    (∀ (e : ProfileBBD) (u : ProfileU), IsStage2EqBBD c (1 / 2) e → IsStage2EqU c (1 / 2) u →
      exAnteA_U c (1 / 2) u < exAnteA_BBD c (1 / 2) e ∧
        exAnteB_U c (1 / 2) u < exAnteB_BBD c (1 / 2) e) := by sorry

end BBDisclosure.Stage2
