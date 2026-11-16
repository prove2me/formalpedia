-- Prove2me | Theorems.Thm_AnonymousDirectedCounting_Exact_Supplement_round_realization_criterion
-- name    : AnonymousDirectedCounting.Exact.Supplement.round_realization_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:53:44.029858+00:00
-- url     : https://prove2.me/theorems/af3ca4be-77e4-49aa-81f9-b7f4cfabfc8b
-- title:
--   Lemma 11 — one-round realizability of full history-prefix data
-- statement:
--   Let $T_{r-1},T_r$ be finite sets of old and new nodes with parent map $\pi:T_r\to T_{r-1}$. Every new node $v$ has anonymity $a(v)\ge1$ and outdegree $d(v)$, and every agent of its fiber must receive $\mu(u,v)$ arcs from the fiber of the old node $u$. Assume the flow equations
--   $$\sum_{v:\pi(v)=u}a(v)d(v)=\sum_{w\in T_r}a(w)\mu(u,w)\qquad(u\in T_{r-1}).\tag{4}$$
--   Put $N=\sum_va(v)$.
--
--   1. If $N>1$, these data have a strongly connected round realization if and only if every new node has positive outdegree $d(v)>0$ and positive incoming degree $\sum_u\mu(u,v)>0$, and the digraph on $T_r$ with an arc $v\to w$ whenever $d(v)>0$ and $\mu(\pi(v),w)>0$ is strongly connected.
--   2. If $N=1$, a strongly connected round realization exists (balance alone suffices).
--
--   The criterion is what the certificate verifier checks on binary node tables without building the network.
--
--   Differences from the source:
--   - generalization: T_{r−1}, T_r are consecutive levels of a proposed full history-tree prefix, with refinement and distinct-signature conventions → arbitrary finite node types and a parent map, without full-prefix syntax conditions; reason: every source instance is included; flow forces unused old nodes to have zero receipts, and the round construction requires only the displayed numerical data
--   - encoding: N agents with fibers and a strongly connected round graph → RoundRealization: f : Fin N → New with fiber sizes a, multiplicities e with the published cut condition; reason: same object; loops and parallel arcs allowed as in the source
--   - encoding: the digraph on T_r is strongly connected → PathConnected (every ordered pair joined by a path); reason: the definition of strong connectivity by paths
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), printed p. 25 (PDF p. 27), Lemma 11

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_Supplement_Rounds

set_option autoImplicit false

open AnonymousDirectedCounting.Exact

namespace AnonymousDirectedCounting.Exact.Supplement

/-- Lemma 11, printed p. 25 (PDF p. 27). Old nodes `Old`, new nodes `New`, parent map `π`, new
anonymities `a(v) ≥ 1`, outdegrees `d(v)`, and required receipts `μ(u, v)` from the fiber of old node
`u` to each agent of `v`, satisfying the flow equations (4). With `N = ∑ a(v)`: for `N > 1` a strongly
connected round realization exists iff every new node has positive outdegree and positive incoming
degree and the digraph on `New` with arcs `v → w` whenever `d(v) > 0` and `μ(π v, w) > 0` is strongly
connected; for `N = 1` a realization always exists. -/
theorem round_realization_criterion {Old New : Type} [Fintype Old] [DecidableEq Old] [Fintype New]
    (π : New → Old) (a d : New → ℕ) (μ : Old → New → ℕ)
    (ha : ∀ v, 1 ≤ a v)
    (hflow : ∀ u : Old,
      ∑ v ∈ Finset.univ.filter (fun v => π v = u), a v * d v = ∑ w, a w * μ u w) :
    (1 < ∑ v, a v →
      (RoundRealization π a d μ ↔
        (∀ v, 0 < d v) ∧ (∀ v, 0 < ∑ u, μ u v) ∧
          PathConnected (fun v w : New => 0 < d v ∧ 0 < μ (π v) w))) ∧
    (∑ v, a v = 1 → RoundRealization π a d μ) := by sorry

end AnonymousDirectedCounting.Exact.Supplement
