-- Prove2me | Theorems.Thm_BorgersMD2015_prop7_6_pad_flexible_dsic_faithful
-- name    : BorgersMD2015.prop7_6_pad_flexible_dsic_faithful
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-23T01:02:31.245133+00:00
-- url     : https://prove2.me/theorems/d5c4e6fd-90e9-43f1-9592-cdc32f5887de
-- title:
--   Proposition 7.6 — flexible PAD rules on the full domain are dominant-strategy implementable
-- statement:
--   Let $I$ be a finite set of agents and $A$ a finite set of alternatives. Agent $i$ has a type set $\Theta_i$ and utility $u_i(a,\theta_i) - t_i$ from alternative $a$ and transfer $t_i$. Suppose the domain is unrestricted: for every $i$ and every vector $\nu \in \mathbb R^{A}$ there is $\theta_i \in \Theta_i$ with $(u_i(a,\theta_i))_{a \in A} = \nu$. Let $q : \Theta \to A$ be a decision rule whose range has at least three elements (flexible) and that satisfies positive association of differences: whenever $q(\theta) = a$ and
--
--   $$u_i(a,\theta'_i) - u_i(b,\theta'_i) > u_i(a,\theta_i) - u_i(b,\theta_i) \quad \text{for all } i \in I \text{ and all } b \ne a,$$
--
--   then $q(\theta') = a$. Then there are transfer rules $t_1, \dots, t_N : \Theta \to \mathbb R$ such that $(q, t_1, \dots, t_N)$ is dominant strategy incentive-compatible.
--
--   This is Proposition 7.6 of Börgers (2015), the sufficiency direction of Roberts' (1979) theorem: on the full utility domain the weak condition PAD already guarantees dominant-strategy implementability, in contrast to the cyclical monotonicity required in general (Proposition 7.1).
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, doi:10.1093/acprof:oso/9780199734023.001.0001, p.135, Proposition 7.6 (Definitions 7.5-7.6 on p.135)

import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model

open MechanismDesign.VCG

theorem BorgersMD2015.prop7_6_pad_flexible_dsic_faithful {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [Finite A] {Θ : ι → Type*} (u : ∀ i, A → Θ i → ℝ)
    (hrich : ∀ (i : ι) (ν : A → ℝ), ∃ θi : Θ i, ∀ a, u i a θi = ν a)
    (q : (∀ i, Θ i) → A) (hflex : Flexible q) (hpad : PAD u q) :
    ∃ t : ι → (∀ i, Θ i) → ℝ, DSIC u ({ q := q, t := t } : DirectMechanism Θ A) := by sorry
