-- Prove2me | Theorems.Thm_ExitSpirals_lemmas_3_6_upper
-- name    : ExitSpirals.lemmas_3_6_upper
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:03:15.405265+00:00
-- url     : https://prove2.me/theorems/36b80378-60c9-4d20-a9d2-d976c10dbcf4
-- title:
--   Lemmas 3 and 6 (corrected: activity bounded by the fixed point of the in-degree system; C1–C3) — upper bound with summable tails
-- statement:
--   Let $p_R,p_C$ be joint degree distributions (in-degree $j$, out-degree $k$, mean degrees in $(0,\infty)$) with $p_{0k,R}=p_{0k,C}=0$ for all $k$ (Assumption 4.5). Let $d_R,d_C$ be well-behaved degree tuples consistent with $p_R$ and $p_C$ (Assumptions A.1, A.2) with asymptotically independent labels. For each $n$, draw $G_R,G_C$ independently and uniformly among simple loopless digraphs with these degrees, and shock each agent independently with probability $1-x$. Let $a(x)=s^*(x)\,g_C(s^*(x))$ be the corrected limit activity, with $s^*(x)$ the greatest fixed point of $F(s,x)=x\,g_R(x\,g_C(s))$.
--
--   Then for every $x\in[0,1]$ and every $\varepsilon>0$,
--   $$\sum_{n}\ \mathbb P\big(\mathcal A_n\ \ge\ a(x)+\varepsilon\big)<\infty,$$
--   where $\mathcal A_n$ is the fraction of agents active in the maximal equilibrium of the random coupled network of size $n$.
--
--   Together with the lower bound (the companion milestone `lemmas_3_6_lower`), this is the asymptotic identification of equilibrium activity with the fixed point of the two-layer branching system that Lemmas 3 and 6 assert.
--
--   Differences from the source:
--   - correction: Lemma 3: for an equilibrium y*, activity ≥ |MGCo(G_R(W), G_C(W))|/n with MGCo the intersection of the two giant out-components (Definition 4.5), and equality in the limit → activity of the maximal equilibrium compared with the corrected fixed-point value a(x); MGCo is not used; reason: on four nodes with R = {1→2, 2→1, 2→3}, C = {3→4, 4→3, 4→1} the giants meet in {1, 3} but the only mutually stable set is ∅, so activity is 0; asymptotically, in the (2,2)-regular case at x = 0.80 the intersection has density ≈ 0.70 while activity is 0. Also y* = 0 is an equilibrium, so 'an equilibrium' must be the maximal one
--   - correction: (9) and Lemma 5: g(f) = 1 − Σ_jk p_jk f^k with H built from p⁺_k = Σ_j (j/λ) p_jk (out-links) → g(s) = 1 − G(1 − s + s f(s)), G(z) = Σ_jk p_jk z^j, f the smallest root of f = H(1 − s + s f) with H built from p⁻_j = Σ_k (k/λ) p_jk (p.46); reason: the printed formula measures who can reach the giant component, but stability needs support from it: with in-degree 2 for all agents and out-degree 0 or 4 with probability ½ (Assumption 4.5 holds), every agent is active at x = 1 by Lemma 2, while the printed g gives ½ − ½f⁴ < ½
--   - correction: Lemma 6: 'activity is then Â(x) := s* = x g_R(x g_C(s*))' → a(x) = s* g_C(s*) = x g_R(s_C) g_C(s_R) with s_R = s*, s_C = x g_C(s*); reason: s* counts agents unshocked with support through R only; activity also needs support through C. In the (2,2)-regular case at x = 0.95, s* = 0.94703 while activity is 0.94406 (simulation with n = 200000: 0.9438, 0.9441)
--   - reading: Lemma 3: 'lim_{n→∞} (1/n) Σ_i y*_i → (1/n)|MGCo|' → the upper half of the limit as Σ_n P(activity ≥ a(x) + ε) < ∞ for every ε > 0; reason: summable tails give lim sup activity ≤ a(x) almost surely under every coupling of the different n (Borel–Cantelli), the strong reading; the lower half is the companion milestone lemmas_3_6_lower
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

open Filter

/-- **Lemmas 3 and 6, corrected: activity is asymptotically at most the fixed-point value
`a(x)`, with summable failure probabilities.**
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814, Lemma 3, p.49
(activity and the mutual giant out-component, "In the limit of large networks we obtain
lim_{n→∞} (1/n) Σ_i y*_i → (1/n)|MGCo(G_R(W), G_C(W))|") and Lemma 6, p.51 (the size is the
greatest solution of (9)).

Let `p_R`, `p_C` be joint degree distributions with `p_{0k} = 0` (Assumption 4.5), let the degree
tuples be well-behaved and consistent with them (Assumptions A.1, A.2) with asymptotically
independent labels, and let `x ∈ [0, 1]`. For every `ε > 0` the probabilities
`P(activity ≥ a(x) + ε)` over `(G_R, G_C, W)` are summable in `n`, where
`a(x) = s*(x) g_C(s*(x))` is `limitActivity`.

**Formalization Note.** The statement replaces the printed equality "activity = |MGCo|/n" by an
asymptotic upper bound for activity in terms of the corrected fixed point; see
`Differences from the source` in the item. -/
theorem lemmas_3_6_upper (pR pC : ℕ → ℕ → ℝ) (hpR : IsDegreeDist pR) (hpC : IsDegreeDist pC)
    (h45R : ∀ k, pR 0 k = 0) (h45C : ∀ k, pC 0 k = 0)
    (dR dC : DegreeTuple) (hdR : WellBehaved dR pR) (hdC : WellBehaved dC pC)
    (hind : IndependentLabels dR dC pR pC)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (ε : ℝ) (hε : 0 < ε) :
    Summable fun n : ℕ =>
      probEvent dR dC x n fun ER EC W => limitActivity pR pC x + ε ≤ activity ER EC W := by sorry

end ExitSpirals
