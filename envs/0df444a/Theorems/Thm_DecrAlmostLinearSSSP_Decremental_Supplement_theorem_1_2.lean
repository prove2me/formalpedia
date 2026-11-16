-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Supplement_theorem_1_2
-- name    : DecrAlmostLinearSSSP.Decremental.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:19:00.305833+00:00
-- url     : https://prove2.me/theorems/5ddead1b-50c0-4e81-888c-c729af830b71
-- title:
--   Theorem 1.2 — Incremental approximate distances and simple source paths
-- statement:
--   There are one deterministic scalar arithmetic program, absolute constants $C>0$ and $Q,P_0\in\mathbb N_{>0}$, and a positive subpolynomial function $a$ with the following guarantee. Let a nonempty finite directed graph have a fixed source $s$, arbitrary initial reachability, integral weights in $[1,W]$ for any real $W\ge1$, and size bound $m\ge n$ on all initially present and subsequently inserted original edges. For every real $0<\epsilon\le1$ and every legal insertion stream, initialization and all updates terminate. At every completed prefix, including the initial graph, all vertices simultaneously have explicit estimates
--
--   $$
--   d_t(v)\le D_t(v)\le(1+\epsilon)d_t(v),\qquad
--   T_{\mathrm{maintenance}}\le C m a(m)\epsilon^{-1}\max\{1,\log_2W\}.
--   $$
--
--   The array is zero at the source and infinite exactly at unreachable vertices. Distance and unreachability queries take at most $Q$ scalar work. For every reachable vertex the program emits a simple source path with
--
--   $$
--   w(P)\le D_t(v)\le(1+\epsilon)d_t(v)
--   $$
--
--   in at most $P_0|P|$ scalar work, for one uniform output constant $P_0$ (the Lean constant is named $P$). Path size counts vertices including the source. Client queries preserve persistent memory; their individual costs add to maintenance work. Every constant and the program are chosen before the graph, $W$, accuracy and stream.
--
--   This is the incremental companion to the existing decremental goal Theorem 1.1, and is not used in that goal's proof. Lemmas 4.1 and 5.1 supply its two supports. There is no external oracle hypothesis here: implementing the rounded-estimate adapter, collecting stable-state writes, and handling arbitrary initial graphs, $n=1$, tiny accuracies and arbitrary $W$ are all proof obligations of this full statement.
--
--   **Formalization Note** The standalone composition in §5.4 chooses $\delta=\epsilon/[4(H+1)]$ and $\widehat m=8m(H+1)$, obtaining $(1+\delta)^{2(H+1)}\le e^{\epsilon/2}\le1+\epsilon$. The full-domain scaling obligations remain in force as detailed in MODERATION_NOTES.md. The displayed log-weight factor uses the conventional positive saturation: at $W=1$ an inserted unit source edge still requires positive work.
--
--   Differences from the source:
--   - encoding: finite directed graph with original positive edge weights and active insertion prefixes → Fin-indexed original edge identifiers with legal disjoint initial and insertion lists and extended nonnegative walk distance; reason: preserves all finite directed instances including parallel edges and entering-source edges; finite weights are embedded in ENNReal and empty feasible walk sets have distance infinity
--   - encoding: deterministic unit-cost data structure with explicit maintained entries and query operations → one finite scalar arithmetic program with prefix-only input, actual terminating executions, explicit memory cells, preserved query memory and charged input delivery; reason: fixes the execution and array layout without assuming correctness, termination or a fast implementation; uniform constants absorb the fixed 32-unit interface charges
--   - encoding: m^(1+o(1)) times the displayed accuracy and weight factors → C m a(m) times the same factors, with a positive and log(a(m))/log(max(2,m)) tending to zero; reason: makes the asymptotic overhead uniform before graph, accuracy, W and streams; only the fixed polynomial-weight exponent may affect constants in Lemma 4.1
--   - encoding: simple path reported in O(|P|), counting vertices including the source → a directed active original-edge walk with duplicate-free vertex list, whose entire vertex/edge transcript is emitted by scalar stores within P(|edges|+1) work; reason: preserves the output-linear guarantee and charges source-only paths, traversal, reversal and emission; there is no unit-cost path oracle
--   - reading: displayed log W in the total-time bound → max(1,log₂ W), retaining every real W≥1; reason: the unweighted two-vertex graph with an inserted unit source edge requires positive work; literal log 1 would give a zero budget, so the asymptotic notation uses a saturated logarithm
--   - encoding: positive integer edge lengths in [1,W] → integer edge lengths with a real numerical upper bound W≥1; reason: integrality applies to the edge lengths, not to the bound; no integer-cap hypothesis is added
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #912 (October 2026), p.3, Theorem 1.2; abstract p.1, general-domain convention p.4, §§4–5 pp.18–36

import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Supplement_Guarantees

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental.Supplement

/-- Theorem 1.2, p.3 and abstract, with all p.4 full-domain reductions remaining proof
obligations: arbitrary initial graphs, every real 0<ε≤1, arbitrary real W≥1 and integral edge weights and n=1.
The conventional log W is max(1,log₂ W), since W=1 must allow positive maintenance work. -/
theorem theorem_1_2 :
    ∃ (p : Program) (C : ℝ) (a : ℕ → ℝ) (Q P : ℕ),
      0 < C ∧ Subpolynomial a ∧ 0 < Q ∧ 0 < P ∧
      ∀ i : Instance, i.Valid → i.Integral →
        ∀ es : List (Fin i.k), i.Legal es → ∃ cs : List Machine,
          Run p i (fun _ => []) es cs ∧
          PathStates p i es cs (1 + i.accuracy) Q P ∧
          WithinBudget i (fun _ => []) es cs (almostLinearBudget C a i true) := by sorry

end DecrAlmostLinearSSSP.Decremental.Supplement
