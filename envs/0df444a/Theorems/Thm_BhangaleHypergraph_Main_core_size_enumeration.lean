-- Prove2me | Theorems.Thm_BhangaleHypergraph_Main_core_size_enumeration
-- name    : BhangaleHypergraph.Main.core_size_enumeration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:08:38.819424+00:00
-- url     : https://prove2.me/theorems/77b01531-56df-44ae-873e-6ea56969e3d1
-- title:
--   Lemma 2.16 — Local core size and enumeration
-- statement:
--   For all $C\ge2$, $s\ge1$ and $R\ge1$, the exact family $U_{C,s}([R])$ is a test domain and
--   $$|U_{C,s}([R])|\le(2R)^{2(C+1)s+C+3}.$$
--   There is one explicit enumeration machine and one absolute positive integer $K$ whose time is bounded by $(2R)^{K(Cs+C+1)}$, uniformly in all valid parameters. Its list contains exactly the membership codes of the core inputs.
--
--   Both the cardinality and effective enumeration clauses are retained.
--
--   Differences from the source:
--   - encoding: one-based finite label and color sets → zero-based Fin types and finite subsets; reason: subtracting one gives a bijection and preserves every instance
--   - encoding: explicit enumeration in asymptotic time → exact bit-string lists output by one TM2 with absolute integer exponents; reason: the list format and uniform bounds express the source enumeration claim without an oracle
--   - encoding: exponent O(Cs+C) → K(Cs+C+1) for one absolute K; reason: Cs+C is positive in the source range, so the added one is absorbed into the same asymptotic exponent
-- source:
--   Amey Bhangale, STOC 2027 submission #1052 (October 2026), Lemma 2.16, p. 11 (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1052.pdf

import Definitions.Def_BhangaleHypergraph_Main_Computation

namespace BhangaleHypergraph.Main

theorem core_size_enumeration :
    (∀ C s R : ℕ, 2 ≤ C → 1 ≤ s → 1 ≤ R →
      TestDomain (Core C s R) ∧ (Core C s R).card ≤ (2 * R) ^ (2 * (C + 1) * s + C + 3)) ∧
    ∃ K : ℕ, 1 ≤ K ∧ ∃ E : CoreRequest → List (List Bool),
      EnumeratesCore E ∧ ComputesWithin CoreRequestCode ListCode E
        (fun x => (2 * max 1 x.2.2) ^ (K * (x.1 * x.2.1 + x.1 + 1))) := by sorry

end BhangaleHypergraph.Main
