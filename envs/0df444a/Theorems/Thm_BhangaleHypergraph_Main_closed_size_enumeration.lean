-- Prove2me | Theorems.Thm_BhangaleHypergraph_Main_closed_size_enumeration
-- name    : BhangaleHypergraph.Main.closed_size_enumeration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:08:28.164436+00:00
-- url     : https://prove2.me/theorems/8e7969e0-f5c7-4f3d-aebd-794ca31287b4
-- title:
--   Lemma 3.2 — Closed domain size and enumeration
-- statement:
--   For a finite layered occurrence system with at most $C+1$ layers, $C\ge2$, $s\ge1$, positive vertex alphabets, and total forward projections, put $M=\max_x R_x$ and let $\Delta$ be maximum occurrence outdegree. Then
--   $$U_{C,s}([R_x])\subseteq W_x,\qquad |W_x|\le(1+\Delta)^C(2M)^{2(C+1)s+C+3},$$
--   and every edge $e:x\to y$ and $B\in W_y$ has $\pi_e^{-1}(B)\in W_x$. All domains consist of subsets of their own label sets.
--
--   One actual machine enumerates the entire domain family in a fixed polynomial in the explicit path bound, the core enumeration bound, and the projection-table representation. Absolute positive integers $K,k$ witness that polynomial uniformly. The output is a list of exactly one domain list per vertex.
--
--   This gives all inclusion, closure, cardinality and enumeration clauses together.
--
--   Differences from the source:
--   - encoding: one-based finite label and color sets → zero-based Fin types and finite subsets; reason: subtracting one gives a bijection and preserves every instance
--   - encoding: explicit enumeration in asymptotic time → exact bit-string lists output by one TM2 with absolute integer exponents; reason: the list format and uniform bounds express the source enumeration claim without an oracle
--   - encoding: polynomial in path/core enumeration bounds and projection tables → the explicit ClosureBudget, using all-vertex path counts and unary table length; reason: multiplication and a fixed natural power express the same polynomial resource bound; maxima of empty data are zero and the empty output is explicit
-- source:
--   Amey Bhangale, STOC 2027 submission #1052 (October 2026), Lemma 3.2, p. 15 (PDF p. 15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1052.pdf

import Definitions.Def_BhangaleHypergraph_Main_Computation

namespace BhangaleHypergraph.Main

theorem closed_size_enumeration :
    (∀ (G : Layered) (C s : ℕ), 2 ≤ C → 1 ≤ s → G.layers ≤ C + 1 →
      (∀ x, Core C s (G.R x) ⊆ Closed G C s x ∧
        (Closed G C s x).card ≤ (1 + MaxOutdegree G) ^ C *
          (2 * MaxAlphabet G) ^ (2 * (C + 1) * s + C + 3)) ∧
      ∀ e, ∀ B ∈ Closed G C s (G.dst e), Preimage (G.proj e) B ∈ Closed G C s (G.src e)) ∧
    ∃ K k : ℕ, 1 ≤ K ∧ 1 ≤ k ∧ ∃ E : ClosedRequest → List (List (List Bool)),
      EnumeratesClosed E ∧ ComputesWithin ClosedRequestCode (fun xs => ListCode (xs.map ListCode))
        E (ClosureBudget K k) := by sorry

end BhangaleHypergraph.Main
