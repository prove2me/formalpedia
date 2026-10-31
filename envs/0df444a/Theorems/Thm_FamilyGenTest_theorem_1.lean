-- Prove2me | Theorems.Thm_FamilyGenTest_theorem_1
-- name    : FamilyGenTest.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:15:19.062246+00:00
-- url     : https://prove2.me/theorems/76a702ee-e9e4-42ee-9266-aea675b83195
-- title:
--   Theorem 1 — the two-sided threshold rule for stopping family testing (corrected: $r_i^\delta = 0$ case)
-- statement:
--   Let $\mathcal I$ be a finite family, let the prior on $\{0,1,2\}^{\mathcal I}$ be arbitrary, let the reward and cost data be arbitrary reals with $r_i^1(0)\le\bar r_i^1(1)$ and $\bar r_i^0(1)\le r_i^0(0)$ for every $i$, and let $\mathbf s$ be a feasible state. Let $\mathbb P_i^{\min}(\mathbf s)$, $\mathbb P_i^{\max}(\mathbf s)$ be the closed-form thresholds of p.ec3, $\mathrm{gap}_i(\mathbf s)$ the net gain function and $Q^*_i(\mathbf s)$ the action value. Write $\mathrm{Stop}(\mathbf s)=\sum_{l\in\mathcal I\setminus\mathbf s}\bar r_l(\mathbb P_l(\mathbf s))$. Then:
--
--   1. For every untested $i$, if the thresholds exist then $\mathbb P_i^{\min}(\mathbf s)\le\mathbb P_i^{\max}(\mathbf s)$.
--   2. For every untested $i$ and every $p\in[0,1]$, $\mathrm{gap}_i(\mathbf s)(p)\ge0$ if and only if the thresholds exist and $\mathbb P_i^{\min}(\mathbf s)\le p\le\mathbb P_i^{\max}(\mathbf s)$.
--   3. For every untested $i$,
--   $$
--   Q^*_i(\mathbf s)-\mathrm{Stop}(\mathbf s)=\mathrm{gap}_i(\mathbf s)(\mathbb P_i(\mathbf s)),
--   $$
--   so $Q^*_i(\mathbf s)\ge\mathrm{Stop}(\mathbf s)$ if and only if the thresholds exist and $\mathbb P_i(\mathbf s)$ lies between them.
--   4. If some untested $i$ has $\mathbb P_i(\mathbf s)$ between its thresholds, then some optimal policy continues testing in $\mathbf s$.
--   5. Otherwise some optimal policy stops in $\mathbf s$, and every optimal policy stops in $\mathbf s$.
--
--   This is the structural result of the paper: the decision to stop testing a family has a two-sided threshold form, and the thresholds carry the value of information through $\Phi_i(\mathbf s)$.
--
--   **Formalization Note** $V^*$ is the maximum of (3), and an optimal policy attains it at every feasible state. In item 4 the policy need not test that particular $i$. At $\mathbb P_i(\mathbf s)=\mathbb P_i^{\min}(\mathbf s)$ both actions can be optimal, which is why item 4 says some optimal policy.
--
--   Differences from the source:
--   - correction: the thresholds divide by $2r_i^\delta$, and Assumption 4 allows $r_i^\delta=0$ → the printed formulas for $r_i^\delta>0$, and for $r_i^\delta=0$ the solution of the linear inequality $Bp-C\ge0$; reason: counterexample satisfying every assumption of the source: $\mathcal I=\{1\}$, $\mathbb P(G_1=0)=\mathbb P(G_1=1)=1/2$, $r^0(0)=1$, $r^1(1)=5$, $r^1(0)=r^0(1)=0$, $\bar r^0(1)=1$, $\bar r^1(1)=0$, $c^s=c^f=1$ has $r^\delta=0$ and the printed formulas are undefined, while testing yields $3/2$ against $1/2$ for stopping
--   - reading: a set of genes $\mathcal J$ in the model of §2; Assumption 4, Assumption 5 and Theorem 1's proof are single-gene → one gene: $g_i\in\{0,1,2\}$; reason: Theorem 1 compares $\mathbb P_i(\mathbf s)$ with two real thresholds, which needs a scalar; its proof, Assumption 4 and §4.3 are single-gene (pp.15, ec2), and no multi-gene threshold statement is printed
--   - reading: "it is optimal to continue testing" → some optimal policy has an action other than stop at $\mathbf s$; reason: at a tie both actions are optimal, so "every optimal policy continues" would be false, and the next person tested need not be $i$
--   - generalization: the Mendelian prior (5) → an arbitrary mass function on $\{0,1,2\}^{\mathcal I}$; reason: the argument does not use the pedigree and p.11 says priors incorporate all prior information; (5) is the special case given by the theorem eq_5_mendelian_prior
--   - generalization: Assumption 4 in full, with Assumptions 1, 2, 3 and stationary, positive, bounded rewards → only $r_i^1(0)\le\bar r_i^1(1)$ and $\bar r_i^0(1)\le r_i^0(0)$; reason: the dropped conditions are not used, and every instance of the source satisfies the two kept inequalities
--   - generalization: "inequality (EC.6) is equivalent to", a statement at the value $\mathbb P_i(\mathbf s)$ → the equivalence for every $p\in[0,1]$; reason: it specializes to $p=\mathbb P_i(\mathbf s)$, and without it "between the thresholds" says nothing beyond (EC.3)
--   - generalization: "otherwise to stop" → some optimal rule stops, and every optimal rule stops; reason: the first half is the source's claim; the second adds to it
--   - generalization: Theorem 1 speaks of two state-dependent thresholds; the closed forms are in its proof → the thresholds are the closed forms, with the identity $Q^*_i(\mathbf s)-\mathrm{Stop}(\mathbf s)=\mathrm{gap}_i(\mathbf s)(\mathbb P_i(\mathbf s))$ as a clause; reason: this implies the printed sentence, and a bare existence claim would be trivial
--   - encoding: a state as a partition $\{s_0,s_1,s_2\}$ of the tested individuals, state space $\mathcal S=\{\mathbf s:\exists g\in\mathcal G(\mathbf s)\}$ → `State I := I → Option (Fin 3)`, with `Feasible` meaning $\mathbb P(G\in\mathcal G(\mathbf s))>0$; reason: same objects when $\mathcal G$ is the support of the prior; the family is a `Fintype`, possibly empty
--   - encoding: $r_i(\mathbb P_i(\mathbf S'))$ with Definition 3 and Assumption 1 → `testedReward`: $r_i^0(0)$ at result $0$, $r_i^1(1)$ at results $1,2$; reason: after a test the belief is the true carrier status, which is what Assumption 1 and Definition 3 give
--   - encoding: $\alpha_i(\mathbf s)$ is a ratio with denominator $\mathbb P_i(\mathbf s)$ → $\alpha_i(\mathbf s)=0$ when the denominator is $0$; reason: the page leaves this case undefined; every use of $\alpha_i$ is then multiplied by $0$
--   - encoding: $V^*$ as the maximum of (3), an expectation over sample paths with absorbing state $\Delta$ and action $C$, undefined at infeasible states → `Vstar`: the maximum over the finite type `Policy I` of the posterior average of a rolled-out return, with no $\Delta$ and no $C$; $V^*=0$ at infeasible states; reason: given $G=g$ and the rule the path is determined, so the two expectations agree; the infeasible children enter only with coefficient $0$
-- source:
--   Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694 (Jan 24 2023), Theorem 1, p.17; thresholds from its proof, pp.ec2–ec3

import Mathlib
import Definitions.Def_FamilyGenTest_Pmax

namespace FamilyGenTest

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- **Theorem 1** (Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694 (Jan 24 2023),
p.17, with the closed-form thresholds of its proof, p.ec3), corrected at `rᵢ^δ = 0`. For a feasible
state `s`:

(a) for untested `i`, if the thresholds exist then `ℙᵢᵐⁱⁿ(s) ≤ ℙᵢᵐᵃˣ(s)`;
(b) for untested `i` and every `p ∈ [0,1]`, the net gain function is `≥ 0` at `p` iff the thresholds
exist and `p` lies between them;
(c) for untested `i`, the advantage of testing `i` over stopping is the net gain function at
`ℙᵢ(s)`, so testing `i` is at least as good as stopping iff `ℙᵢ(s)` lies between the thresholds;
(d) if some untested `i` has `ℙᵢ(s)` between its thresholds, some optimal rule continues in `s`;
(e) otherwise some optimal rule stops in `s`, and every optimal rule stops in `s`.

**Formalization Note** Only the two weak inequalities `CensoredOrder` of Assumption 4 are assumed;
the prior is arbitrary. `V*` is the maximum of (3). -/
theorem theorem_1 (R : Rewards I) (μ : Prior I) (hR : CensoredOrder R) (s : State I)
    (hs : Feasible μ s) :
    (∀ i, s i = none → ThresholdsExist R μ s i → Pmin R μ s i ≤ Pmax R μ s i) ∧
    (∀ i, s i = none → ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      (0 ≤ gap R μ s i p ↔
        ThresholdsExist R μ s i ∧ Pmin R μ s i ≤ p ∧ p ≤ Pmax R μ s i)) ∧
    (∀ i, s i = none →
      Qstar R μ s i - stopValue R μ s = gap R μ s i (risk μ s i) ∧
      (stopValue R μ s ≤ Qstar R μ s i ↔ RiskBetween R μ s i)) ∧
    ((∃ i, s i = none ∧ RiskBetween R μ s i) →
      ∃ π : Policy I, IsOptimal R μ π ∧ π.1 s ≠ none) ∧
    ((¬ ∃ i, s i = none ∧ RiskBetween R μ s i) →
      (∃ π : Policy I, IsOptimal R μ π ∧ π.1 s = none) ∧
      ∀ π : Policy I, IsOptimal R μ π → π.1 s = none) := by sorry

end FamilyGenTest
