-- Prove2me | Theorems.Thm_ExitSpirals_lemmas_3_6_lower
-- name    : ExitSpirals.lemmas_3_6_lower
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:03:24.160967+00:00
-- url     : https://prove2.me/theorems/2b9b6ac4-a2b8-4eb5-a61b-2db38fbd7cb0
-- title:
--   Lemmas 3 and 6 (corrected: activity bounded by the fixed point of the in-degree system; C1–C3) — lower bound against $a(x')$, $x'<x$
-- statement:
--   Let $p_R,p_C$ be joint degree distributions (in-degree $j$, out-degree $k$, mean degrees in $(0,\infty)$) with $p_{0k,R}=p_{0k,C}=0$ for all $k$ (Assumption 4.5). Let $d_R,d_C$ be well-behaved degree tuples consistent with $p_R$ and $p_C$ (Assumptions A.1, A.2) with asymptotically independent labels. For each $n$, draw $G_R,G_C$ independently and uniformly among simple loopless digraphs with these degrees, and shock each agent independently with probability $1-x$. Let $a(x)=s^*(x)\,g_C(s^*(x))$ be the corrected limit activity, with $s^*(x)$ the greatest fixed point of $F(s,x)=x\,g_R(x\,g_C(s))$.
--
--   Then for all $0\le x'<x\le1$ and every $\varepsilon>0$,
--   $$\mathbb P\big(\mathcal A_n(x)\ \ge\ a(x')-\varepsilon\big)\ \longrightarrow\ 1\qquad(n\to\infty),$$
--   where $\mathcal A_n(x)$ is the activity of the random coupled network of size $n$ under a shock of size $1-x$.
--
--   With the upper bound (`lemmas_3_6_upper`) it gives $\mathcal A_n(x)\to a(x)$ in probability at every $x$ where $a$ is left-continuous; in particular activity is asymptotically at least $a(x')$ whenever the shock is strictly smaller than $1-x'$.
--
--   Differences from the source:
--   - correction: Lemma 3: for an equilibrium y*, activity ≥ |MGCo(G_R(W), G_C(W))|/n with MGCo the intersection of the two giant out-components (Definition 4.5), and equality in the limit → activity of the maximal equilibrium compared with the corrected fixed-point value a(x); MGCo is not used; reason: on four nodes with R = {1→2, 2→1, 2→3}, C = {3→4, 4→3, 4→1} the giants meet in {1, 3} but the only mutually stable set is ∅, so activity is 0; asymptotically, in the (2,2)-regular case at x = 0.80 the intersection has density ≈ 0.70 while activity is 0. Also y* = 0 is an equilibrium, so 'an equilibrium' must be the maximal one
--   - correction: (9) and Lemma 5: g(f) = 1 − Σ_jk p_jk f^k with H built from p⁺_k = Σ_j (j/λ) p_jk (out-links) → g(s) = 1 − G(1 − s + s f(s)), G(z) = Σ_jk p_jk z^j, f the smallest root of f = H(1 − s + s f) with H built from p⁻_j = Σ_k (k/λ) p_jk (p.46); reason: the printed formula measures who can reach the giant component, but stability needs support from it: with in-degree 2 for all agents and out-degree 0 or 4 with probability ½ (Assumption 4.5 holds), every agent is active at x = 1 by Lemma 2, while the printed g gives ½ − ½f⁴ < ½
--   - correction: Lemma 6: 'activity is then Â(x) := s* = x g_R(x g_C(s*))' → a(x) = s* g_C(s*) = x g_R(s_C) g_C(s_R) with s_R = s*, s_C = x g_C(s*); reason: s* counts agents unshocked with support through R only; activity also needs support through C. In the (2,2)-regular case at x = 0.95, s* = 0.94703 while activity is 0.94406 (simulation with n = 200000: 0.9438, 0.9441)
--   - correction: Lemma 3: 'lim_{n→∞} (1/n) Σ_i y*_i → (1/n)|MGCo|' at every x → the lower half as P(activity at x ≥ a(x′) − ε) → 1 for every x′ < x; reason: a(x) jumps at x_crit (Proposition 3), and at the jump the page gives no argument that the finite systems reach a(x_crit) rather than collapse; the one-sided bound against x′ < x, together with lemmas_3_6_upper, gives the limit at every left-continuity point of a, which includes every x ≠ x_crit used by the goal. At x = x_crit the printed limit fails; take p_R = p_C = δ_(1,1) (x_crit = 1, a(1) = 1) and tuples in which ⌊√n⌋ agents have (in, out) = (0, 1), ⌊√n⌋ have (1, 0) and the rest (1, 1) in G_R, (1, 1) for all in G_C; the tuples are well-behaved with independent labels, but at x = 1 only agents on R-cycles can be active, and these are a vanishing fraction (simulated fraction 0.0002 to 0.0021 at n = 10⁶), so activity → 0 ≠ a(1); in the tangent case the same happens for tuples whose empirical laws approach p from the subcritical side slowly
--   - correction: Assumptions 4.1–4.2: i.i.d. costs with F(c, x) = x for c < b + ϵ and 1 otherwise, and a benefit function b → the best response (4) is the primitive, with a shocked set W containing each agent independently with probability 1 − x; reason: as printed F(·, x) is not a distribution function (it does not tend to 0 as c → −∞ for x > 0) and contradicts F(0; x) = 0 of Assumption 2.1(1); p.22 states that under these assumptions a uniformly random fraction 1 − x of agents is shocked and the best response is (4), which is what the Lean statement uses
--   - reading: A.3, p.47: p_{jk,n} with j the out-degree and k the in-degree → j the in-degree and k the out-degree, for the empirical and the limit law; reason: pp.16 and 25 and the gloss of Assumption 4.5 ('each node has at least one incoming link') define p_jk with j the in-degree; A.3's order contradicts them
--   - reading: p.48: the two tuples 'are viewed as random variables', and Assumption 3.1 'implies' independence of the degrees (garbled sentence) → every pair of deterministic well-behaved tuples whose joint empirical law of (d⁻_R, d⁺_R, d⁻_C, d⁺_C) converges to p_R ⊗ p_C; reason: this covers every typical realization of independently drawn tuples, and it cannot be dropped: with in-degree 1 or 3 with probability ½ the fixed-point threshold is 0.9965 for independent labels and 0.9705 when each agent has the same in-degree in both networks
--   - reading: Assumption A.2(2): Δ_n ≤ n^{1/12}/log n → for all sufficiently large n; reason: at n = 1 log n = 0 and any degree ≥ 1 violates the bound until n is astronomically large, so a literal 'for all n' makes the class of well-behaved tuples empty; Cooper–Frieze's conditions are asymptotic and §4.3.1 studies n sufficiently large
--   - encoding: agents N = {1, …, n}; a network as a set of directed links, i → j supporting j → agents Fin n; a network is a Finset of pairs, (j, i) ∈ E meaning j → i; reason: same objects; a Finset has no multiple links, as A.3 conditions on simple graphs
--   - encoding: G_µ a uniform draw from G(n, d⁺_µ, d⁻_µ), independent across µ and of the costs → an explicit finite average over graphsWith with weights |G_R|⁻¹|G_C|⁻¹∏_i(1 − x or x); weight 0 when a degree set is empty; reason: the same law whenever G(n, d⁺, d⁻) is nonempty, which the source presupposes; an empty set only lowers probabilities
-- source:
--   Aymanns, Georg, Golub, Exit Spirals in Coupled Networked Markets, SSRN 2881814 (preprint, sha256 12000f11…6c84d2), Lemma 3, p.49; Lemma 6, p.51 (corrected)

import Mathlib
import Definitions.Def_ExitSpirals_activity
import Definitions.Def_ExitSpirals_IsDegreeDist
import Definitions.Def_ExitSpirals_WellBehaved
import Definitions.Def_ExitSpirals_probEvent
import Definitions.Def_ExitSpirals_coupledMap

namespace ExitSpirals

open Filter Topology

/-- **Lemmas 3 and 6, corrected: activity at `x` is asymptotically at least the fixed-point value
`a(x′)` for any `x′ < x`.**
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814, Lemma 3, p.49 and
Lemma 6, p.51.

Under the hypotheses of `lemmas_3_6_upper`, for all `0 ≤ x′ < x ≤ 1` and `ε > 0`,
`P(activity at shock x ≥ a(x′) − ε) → 1` as `n → ∞`.

**Formalization Note.** The bound compares activity at `x` with the fixed point at a smaller
`x′`, so that no limit is claimed at a jump of `a`. Together with `lemmas_3_6_upper` it gives the
convergence of activity to `a(x)` at every continuity point of `a`. -/
theorem lemmas_3_6_lower (pR pC : ℕ → ℕ → ℝ) (hpR : IsDegreeDist pR) (hpC : IsDegreeDist pC)
    (h45R : ∀ k, pR 0 k = 0) (h45C : ∀ k, pC 0 k = 0)
    (dR dC : DegreeTuple) (hdR : WellBehaved dR pR) (hdC : WellBehaved dC pC)
    (hind : IndependentLabels dR dC pR pC)
    (x' x : ℝ) (hx' : x' ∈ Set.Icc (0 : ℝ) 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hlt : x' < x)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      probEvent dR dC x n fun ER EC W => limitActivity pR pC x' - ε ≤ activity ER EC W)
      atTop (𝓝 1) := by sorry

end ExitSpirals
