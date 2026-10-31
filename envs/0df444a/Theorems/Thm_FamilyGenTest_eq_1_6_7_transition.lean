-- Prove2me | Theorems.Thm_FamilyGenTest_eq_1_6_7_transition
-- name    : FamilyGenTest.eq_1_6_7_transition
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:12:11.681069+00:00
-- url     : https://prove2.me/theorems/7afadc9d-8ce7-405a-a442-c93079426e70
-- title:
--   Eqs (1), (6), (7) — the transition probability is the marginal
-- statement:
--   Let $\mathbf s$ be feasible and $i$ untested in $\mathbf s$. Then for every $\gamma\in\{0,1,2\}$ the transition probability (1) to $\mathbf s_\gamma\cup\{i\}$ is the marginal (6),
--   $$
--   \mathbb P\bigl(G\in\mathcal G(\mathbf s_\gamma\cup\{i\})\mid G\in\mathcal G(\mathbf s)\bigr)=\mathbb P(G_i=\gamma\mid\mathbf s),
--   $$
--   these sum to $1$ over $\gamma$, and for every genotype $g$,
--   $$
--   \mu(g\mid\mathbf s)=\mathbb P(G_i=g_i\mid\mathbf s)\,\mu(g\mid\mathbf s_{g_i}\cup\{i\}).
--   $$
--
--   The last identity says that updating the posterior by (7) one step at a time agrees with conditioning at once, which is what makes the rolled-out return of (3) a dynamic program.
--
--   Differences from the source:
--   - reading: a set of genes $\mathcal J$ in the model of §2; Assumption 4, Assumption 5 and Theorem 1's proof are single-gene → one gene: $g_i\in\{0,1,2\}$; reason: Theorem 1 compares $\mathbb P_i(\mathbf s)$ with two real thresholds, which needs a scalar; its proof, Assumption 4 and §4.3 are single-gene (pp.15, ec2), and no multi-gene threshold statement is printed
--   - generalization: the Mendelian prior (5) → an arbitrary mass function on $\{0,1,2\}^{\mathcal I}$; reason: the argument does not use the pedigree and p.11 says priors incorporate all prior information; (5) is the special case given by the theorem eq_5_mendelian_prior
--   - encoding: a state as a partition $\{s_0,s_1,s_2\}$ of the tested individuals, state space $\mathcal S=\{\mathbf s:\exists g\in\mathcal G(\mathbf s)\}$ → `State I := I → Option (Fin 3)`, with `Feasible` meaning $\mathbb P(G\in\mathcal G(\mathbf s))>0$; reason: same objects when $\mathcal G$ is the support of the prior; the family is a `Fintype`, possibly empty
-- source:
--   Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694 (Jan 24 2023), (1), p.8; (6), (7), p.12

import Mathlib
import Definitions.Def_FamilyGenTest_risk

namespace FamilyGenTest

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Eqs (1), (6), (7) (Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694
(Jan 24 2023), pp.8, 12). For a feasible `s` and an untested `i`: the transition probability
`ℙ(G ∈ 𝒢(s′) | G ∈ 𝒢(s))` to `s′ = s` with `i ↦ γ` is the marginal `ℙ(Gᵢ = γ | s)`; these sum to `1`;
and the posterior of `s` is that marginal times the posterior (7) of the next state. -/
theorem eq_1_6_7_transition (μ : Prior I) (s : State I) (hs : Feasible μ s) (i : I)
    (hi : s i = none) :
    (∀ γ, mass μ (test s i γ) / mass μ s = marginal μ s i γ) ∧
    ∑ γ, marginal μ s i γ = 1 ∧
    ∀ g, posterior μ s g = marginal μ s i (g i) * posterior μ (test s i (g i)) g := by sorry

end FamilyGenTest
