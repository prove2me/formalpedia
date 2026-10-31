-- Prove2me | Theorems.Thm_FamilyGenTest_threshold_equivalence
-- name    : FamilyGenTest.threshold_equivalence
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:59.385777+00:00
-- url     : https://prove2.me/theorems/07e1f8e5-8e53-42c6-b509-a7b0cd8d5cec
-- title:
--   Threshold equivalence, p.ec3 (corrected: $r_i^\delta = 0$ case)
-- statement:
--   For real $A\ge0$, $B$, $C$: if the thresholds of $(A,B,C)$ exist, the lower one is at most the upper one; and for every $p\in[0,1]$,
--   $$
--   -Ap^2+Bp-C\ge0
--   $$
--   if and only if the thresholds exist and $p$ lies between them. In particular, under the two weak inequalities of Assumption 4, for every state $\mathbf s$ and person $i$: if the thresholds exist then $\mathbb P_i^{\min}(\mathbf s)\le\mathbb P_i^{\max}(\mathbf s)$, and for every $p\in[0,1]$,
--   $$
--   \mathrm{gap}_i(\mathbf s)(p)\ge0\iff\text{the thresholds exist and }\mathbb P_i^{\min}(\mathbf s)\le p\le\mathbb P_i^{\max}(\mathbf s).
--   $$
--
--   The thresholds are thus a property of the quadratic and not of the single value $\mathbb P_i(\mathbf s)$.
--
--   Differences from the source:
--   - correction: the thresholds divide by $2r_i^\delta$, and Assumption 4 allows $r_i^\delta=0$ → the printed formulas for $r_i^\delta>0$, and for $r_i^\delta=0$ the solution of the linear inequality $Bp-C\ge0$; reason: counterexample satisfying every assumption of the source: $\mathcal I=\{1\}$, $\mathbb P(G_1=0)=\mathbb P(G_1=1)=1/2$, $r^0(0)=1$, $r^1(1)=5$, $r^1(0)=r^0(1)=0$, $\bar r^0(1)=1$, $\bar r^1(1)=0$, $c^s=c^f=1$ has $r^\delta=0$ and the printed formulas are undefined, while testing yields $3/2$ against $1/2$ for stopping
--   - reading: a set of genes $\mathcal J$ in the model of §2; Assumption 4, Assumption 5 and Theorem 1's proof are single-gene → one gene: $g_i\in\{0,1,2\}$; reason: Theorem 1 compares $\mathbb P_i(\mathbf s)$ with two real thresholds, which needs a scalar; its proof, Assumption 4 and §4.3 are single-gene (pp.15, ec2), and no multi-gene threshold statement is printed
--   - generalization: the Mendelian prior (5) → an arbitrary mass function on $\{0,1,2\}^{\mathcal I}$; reason: the argument does not use the pedigree and p.11 says priors incorporate all prior information; (5) is the special case given by the theorem eq_5_mendelian_prior
--   - generalization: Assumption 4 in full, with Assumptions 1, 2, 3 and stationary, positive, bounded rewards → only $r_i^1(0)\le\bar r_i^1(1)$ and $\bar r_i^0(1)\le r_i^0(0)$; reason: the dropped conditions are not used, and every instance of the source satisfies the two kept inequalities
--   - generalization: "inequality (EC.6) is equivalent to", a statement at the value $\mathbb P_i(\mathbf s)$ → the equivalence for every $p\in[0,1]$; reason: it specializes to $p=\mathbb P_i(\mathbf s)$, and without it "between the thresholds" says nothing beyond (EC.3)
--   - encoding: a state as a partition $\{s_0,s_1,s_2\}$ of the tested individuals, state space $\mathcal S=\{\mathbf s:\exists g\in\mathcal G(\mathbf s)\}$ → `State I := I → Option (Fin 3)`, with `Feasible` meaning $\mathbb P(G\in\mathcal G(\mathbf s))>0$; reason: same objects when $\mathcal G$ is the support of the prior; the family is a `Fintype`, possibly empty
--   - encoding: $\alpha_i(\mathbf s)$ is a ratio with denominator $\mathbb P_i(\mathbf s)$ → $\alpha_i(\mathbf s)=0$ when the denominator is $0$; reason: the page leaves this case undefined; every use of $\alpha_i$ is then multiplied by $0$
--   - encoding: $V^*$ as the maximum of (3), an expectation over sample paths with absorbing state $\Delta$ and action $C$, undefined at infeasible states → `Vstar`: the maximum over the finite type `Policy I` of the posterior average of a rolled-out return, with no $\Delta$ and no $C$; $V^*=0$ at infeasible states; reason: given $G=g$ and the rule the path is determined, so the two expectations agree; in $\Phi_i$ and $\mathrm{gap}_i$ the infeasible children enter only with coefficient $0$, and in the thresholds the value $V^*(\mathbf s_0\cup\{i\})=0$ at $\mathbb P_i(\mathbf s)=1$ fills a value the page leaves undefined
-- source:
--   Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694 (Jan 24 2023), Proof of Theorem 1, p.ec3, "inequality (EC.6) is equivalent to"

import Mathlib
import Definitions.Def_FamilyGenTest_Pmax

namespace FamilyGenTest

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The threshold equivalence (Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694
(Jan 24 2023), p.ec3, "inequality (EC.6) is equivalent to"), corrected at `rᵢ^δ = 0`. For real
`A ≥ 0`, `B`, `C`: if the thresholds exist they are ordered, and for every `p ∈ [0,1]`,
`−Ap² + Bp − C ≥ 0` iff they exist and `p` lies between them. The second part instantiates this for
the model, for every state. -/
theorem threshold_equivalence :
    (∀ A B C : ℝ, 0 ≤ A →
      (QuadExists A B C → quadMin A B C ≤ quadMax A B C) ∧
      ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
        (0 ≤ -A * p ^ 2 + B * p - C ↔
          QuadExists A B C ∧ quadMin A B C ≤ p ∧ p ≤ quadMax A B C)) ∧
    ∀ (R : Rewards I) (μ : Prior I) (s : State I) (i : I), CensoredOrder R →
      (ThresholdsExist R μ s i → Pmin R μ s i ≤ Pmax R μ s i) ∧
      ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
        (0 ≤ gap R μ s i p ↔
          ThresholdsExist R μ s i ∧ Pmin R μ s i ≤ p ∧ p ≤ Pmax R μ s i) := by sorry

end FamilyGenTest
