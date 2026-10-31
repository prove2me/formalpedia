-- Prove2me | Theorems.Thm_ExitSpirals_proposition_3
-- name    : ExitSpirals.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:03:46.53566+00:00
-- url     : https://prove2.me/theorems/185c583f-17b1-4a67-8cb9-5645fedf6de7
-- title:
--   Proposition 3 (corrected: best response (4) as primitive, C5) — two independent random networks with simple complementarities lose all activity discontinuously at a critical shock
-- statement:
--   Let $p_R,p_C$ be joint degree distributions of the two markets ($p_{jk}$ = fraction of agents with in-degree $j$ and out-degree $k$, mean degree in $(0,\infty)$) with $p_{0k,R}=p_{0k,C}=0$ for all $k$ (Assumption 4.5: every agent has an in-link in both markets). Then there exist
--   $$x_{crit}\in(0,1]\quad\text{and}\quad A_{crit}>0,$$
--   depending only on $p_R,p_C$, with the following property. Let $d_R,d_C$ be any well-behaved degree tuples consistent with $p_R,p_C$ (Assumptions A.1, A.2) with asymptotically independent labels. For each $n$ draw $G_R$ and $G_C$ independently and uniformly among the simple loopless digraphs on $n$ agents with these degrees, and shock each agent independently with probability $1-x$. Let $\mathcal A_n(x)$ be the fraction of agents active in the maximal equilibrium of the best response (4): an agent is active iff it is unshocked and has an active supporter in each market. Then
--
--   1. for every $x\in[0,1]$ with $x>x_{crit}$:
--   $$\mathbb P\big(\mathcal A_n(x)\ge A_{crit}\big)\longrightarrow1;$$
--   2. for every $x\in[0,1]$ with $x<x_{crit}$:
--   $$\mathbb E\big[\mathcal A_n(x)\big]\longrightarrow0\qquad\text{and}\qquad \sum_n\mathbb P\big(\mathcal A_n(x)\ge\varepsilon\big)<\infty\ \text{ for every }\varepsilon>0.$$
--
--   That is, there is an **exit spiral** at $x_{crit}$ in the sense of Definition 3.1: activity is bounded below by a fixed $A_{crit}>0$ for every shock smaller than $1-x_{crit}$, and vanishes for every larger shock, so it drops discontinuously from at least $A_{crit}$ to $0$.
--
--   **Formalization Note** Agents are `Fin n` and networks `Finset`s of links. The best response (4) is the primitive of the game, with Bernoulli$(1-x)$ shocks. Definition 3.1 is stated for the limit activity $\hat{\mathcal A}$; here "asymptotically almost surely" is probability tending to one, and "almost surely $\hat{\mathcal A}=0$" is convergence of the expected activity to $0$ together with summable tail probabilities, which gives almost-sure convergence to $0$ under every coupling of the different $n$. $x_{crit}$ and $A_{crit}$ are chosen before the degree tuples and $A_{crit}$ before $x$, so the gap is uniform.
--
--   Differences from the source:
--   - correction: Assumptions 4.1–4.2: i.i.d. costs with F(c, x) = x for c < b + ϵ and 1 otherwise, and a benefit function b → the best response (4) is the primitive, with a shocked set W containing each agent independently with probability 1 − x; reason: as printed F(·, x) is not a distribution function (it does not tend to 0 as c → −∞ for x > 0) and contradicts F(0; x) = 0 of Assumption 2.1(1); p.22 states that under these assumptions a uniformly random fraction 1 − x of agents is shocked and the best response is (4), which is what the Lean statement uses
--   - reading: A.3, p.47: p_{jk,n} with j the out-degree and k the in-degree → j the in-degree and k the out-degree, for the empirical and the limit law; reason: pp.16 and 25 and the gloss of Assumption 4.5 ('each node has at least one incoming link') define p_jk with j the in-degree; A.3's order contradicts them
--   - reading: Definition 3.1(2): 'Â = 0 almost surely' for x < x_crit → E[activity] → 0 and Σ_n P(activity ≥ ε) < ∞ for every ε > 0; reason: at finite n activity is positive with positive probability (two unshocked agents forming a 2-cycle in both networks stay active), so Â is the limit fraction (p.27) or the expectation (p.15); summable tails give almost-sure convergence to 0 under every coupling of the different n (Borel–Cantelli), the strong reading, and imply convergence in probability
--   - reading: Definition 3.1(1): 'Â ≥ A_crit asymptotically almost surely' for x > x_crit → P(activity ≥ A_crit) → 1 as n → ∞; reason: the standard meaning of 'asymptotically almost surely'
--   - reading: p.48: the two tuples 'are viewed as random variables', and Assumption 3.1 'implies' independence of the degrees (garbled sentence) → every pair of deterministic well-behaved tuples whose joint empirical law of (d⁻_R, d⁺_R, d⁻_C, d⁺_C) converges to p_R ⊗ p_C; reason: this covers every typical realization of independently drawn tuples, and it cannot be dropped: with in-degree 1 or 3 with probability ½ the fixed-point threshold is 0.9965 for independent labels and 0.9705 when each agent has the same in-degree in both networks
--   - reading: Assumption A.2(2): Δ_n ≤ n^{1/12}/log n → for all sufficiently large n; reason: at n = 1 log n = 0 and any degree ≥ 1 violates the bound until n is astronomically large, so a literal 'for all n' makes the class of well-behaved tuples empty; Cooper–Frieze's conditions are asymptotic and §4.3.1 studies n sufficiently large
--   - generalization: Assumption 4.6 (giant component concavity) → not assumed; reason: its only use is Lemma 10(4), which serves to count fixed points; the conclusion holds without it, and adding it gives the source's statement
--   - generalization: Assumption 4.3 (every agent has an incoming edge in G_R and G_C) → only its limit form Assumption 4.5 (p_0k = 0) is assumed; reason: o(n) agents may have in-degree 0; tuples satisfying Assumption 4.3 are a special case
--   - generalization: x_crit (no range stated in Proposition 3) → x_crit ∈ (0, 1]; reason: a stronger conclusion; Proposition 1 states 0 < x_crit for its setting. x_crit < 1 is not claimed: p.56 allows the case where any shock causes complete collapse (e.g. p_11 = 1)
--   - generalization: Definition 3.1: 'Fix the parameters of the environment' → x_crit and A_crit depend only on p_R, p_C and are chosen before the degree tuples; reason: the tuples are random variables (p.48), so the environment is the pair of laws; uniformity over the tuples implies the statement for each fixed tuple
--   - encoding: agents N = {1, …, n}; a network as a set of directed links, i → j supporting j → agents Fin n; a network is a Finset of pairs, (j, i) ∈ E meaning j → i; reason: same objects; a Finset has no multiple links, as A.3 conditions on simple graphs
--   - encoding: G_µ a uniform draw from G(n, d⁺_µ, d⁻_µ), independent across µ and of the costs → an explicit finite average over graphsWith with weights |G_R|⁻¹|G_C|⁻¹∏_i(1 − x or x); weight 0 when a degree set is empty; reason: the same law whenever G(n, d⁺, d⁻) is nonempty, which the source presupposes; an empty set only lowers probabilities
-- source:
--   Aymanns, Georg, Golub, Exit Spirals in Coupled Networked Markets, SSRN 2881814 (preprint, sha256 12000f11…6c84d2), Proposition 3, p.27; Definition 3.1, p.17; standing assumptions of §4 (pp.21–27) and Appendix A.3 (pp.47–48)

import Mathlib
import Definitions.Def_ExitSpirals_activity
import Definitions.Def_ExitSpirals_IsDegreeDist
import Definitions.Def_ExitSpirals_WellBehaved
import Definitions.Def_ExitSpirals_probEvent

namespace ExitSpirals

open Filter Topology

/-- **Proposition 3 (exit spiral in coupled networked markets with simple complementarities).**
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814, Proposition 3,
p.27: "Under the assumptions in this section, in coupled networked markets with complementarities,
there is an exit spiral at some x_crit, as defined in Definition 3.1." Definition 3.1, p.17: "We say
an exit spiral occurs at x_crit, if: 1. There is an A_crit > 0 such that whenever x > x_crit, we
have Â ≥ A_crit asymptotically almost surely; 2. For x < x_crit, the activity measure satisfies
Â = 0 almost surely."

For all joint degree distributions `p_R`, `p_C` with `p_{0k} = 0` (Assumption 4.5) there are
`x_crit ∈ (0, 1]` and `A_crit > 0` such that for every pair of well-behaved degree-sequence
tuples consistent with `p_R`, `p_C` and with asymptotically independent labels, where `G_R`, `G_C`
are independent uniform simple digraphs with the given degrees and each agent is shocked
independently with probability `1 − x`:
1. for every `x ∈ [0, 1]` with `x > x_crit`, `P(activity ≥ A_crit) → 1` as `n → ∞`;
2. for every `x ∈ [0, 1]` with `x < x_crit`, the expected activity tends to `0`, and for every
   `ε > 0`, `Σ_n P(activity ≥ ε) < ∞`.

**Formalization Note.** Agents are `Fin n`, networks are `Finset`s of links; `p j k` has `j` the
in-degree and `k` the out-degree (pp.16, 25); the best response (4) is the primitive with
Bernoulli(1 − x) shocks; activity is the fraction active in the maximal equilibrium at finite
`n`, and `Â` of Definition 3.1 is read as its limit: "asymptotically almost surely" as probability
tending to one, "almost surely" as convergence of the expectation together with summable tails
(almost sure convergence under every coupling of the `n`, by Borel–Cantelli). `x_crit` and
`A_crit` depend on `p_R`, `p_C` only, and `A_crit` is uniform in `x`. -/
theorem proposition_3 :
    ∀ pR pC : ℕ → ℕ → ℝ, IsDegreeDist pR → IsDegreeDist pC →
      (∀ k, pR 0 k = 0) → (∀ k, pC 0 k = 0) →
      ∃ xcrit ∈ Set.Ioc (0 : ℝ) 1, ∃ Acrit : ℝ, 0 < Acrit ∧
        ∀ dR dC : DegreeTuple, WellBehaved dR pR → WellBehaved dC pC →
          IndependentLabels dR dC pR pC →
          (∀ x ∈ Set.Icc (0 : ℝ) 1, xcrit < x →
            Tendsto (fun n : ℕ =>
              probEvent dR dC x n fun ER EC W => Acrit ≤ activity ER EC W) atTop (𝓝 1)) ∧
          (∀ x ∈ Set.Icc (0 : ℝ) 1, x < xcrit →
            Tendsto (fun n : ℕ => expectedActivity dR dC x n) atTop (𝓝 0) ∧
            ∀ ε : ℝ, 0 < ε → Summable fun n : ℕ =>
              probEvent dR dC x n fun ER EC W => ε ≤ activity ER EC W) := by sorry

end ExitSpirals
