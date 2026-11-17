-- Prove2me | Theorems.Thm_ForgetAlt_Supplement_theorem_5_1
-- name    : ForgetAlt.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:18:00.194587+00:00
-- url     : https://prove2.me/theorems/34164eb5-212f-434c-8363-94bfeb935407
-- title:
--   Theorem 5.1: maximal disjoint shortest augmenting paths in $O(m\log n)$ and an MCM in $O(m\sqrt n\log n)$
-- statement:
--   Let $G$ be a graph with $n$ vertices and $m$ edges and $M$ a matching of $G$.
--
--   1. A **maximal** set of vertex-disjoint shortest augmenting paths of $(G,M)$ can be computed in time
--   $$O(m\log n).$$
--   2. Consequently, a maximum-cardinality matching of $G$ can be computed in time
--   $$O(m\sqrt n\,\log n).$$
--
--   Both claims are about the word RAM with $O(\log n)$-bit words. The first clause is unconditional: it does not assume a double path algorithm, unlike Theorem 1.1. The second clause gives an MCM algorithm within a logarithmic factor of the Micali–Vazirani bound, via the Hopcroft–Karp phase analysis.
--
--   **Formalization Note** One program per clause of the published word RAM `EndStatement`; time is the number of steps; the bounds are $C(m\lfloor\log_2 n\rfloor+1)$ and $C(m\lfloor\sqrt n\rfloor\lfloor\log_2 n\rfloor+1)$, and every graph on $n$ vertices is allowed, isolated vertices included.
--
--   Differences from the source:
--   - reading: “computed in O(·) time” → a program of the published word RAM EndStatement (step count), correct at every word width W ≥ b·(⌊log₂(n + m + 2)⌋ + 1), one program B with constants b, C for all instances; reason: the paper's model is the word RAM with O(log n)-bit words; same convention as the base mission's ForgetAlt.Machine
--   - reading: O(m log n) and O(m√n log n) → ≤ C·(m·⌊log₂ n⌋ + 1) and ≤ C·(m·⌊√n⌋·⌊log₂ n⌋ + 1); reason: the + 1 only matters when the bound is 0; ⌊√n⌋ ≥ √n/2 for n ≥ 1 and ⌊log₂ n⌋ ≥ (log₂ n)/2 for n ≥ 2, and a graph with n ≤ 1 has no edge
--   - encoding: a matching system I = (G, M); an MCM of G → the base AugProblem true layout (edge triples with a matching flag; output the paths); a new MCMProblem layout (edge pairs; output the number of edges and the edges, distinct, forming a matching of size µ(G)); reason: fixed word layouts; no condition beyond the problem statement
--   - generalization: “Throughout this subsection, we assume that G has no isolated vertex … Thus n ≤ 2m holds” (§5.1 preamble, p.47; “Recall that n ≤ 2m holds”, proof, p.48) → every graph on Fin n, isolated vertices allowed, and no n term in either bound; reason: on graphs without isolated vertices (the source's case) n ≤ 2m, so the Lean bounds are the source's; the paper calls isolated vertices irrelevant to matchings, word RAM memory starts at zero, so a program need not touch them (the base mission's reading of the same sentence for Theorem 1.1)
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Theorem 5.1, printed p.48 (PDF p.49)

import Mathlib
import Definitions.Def_ForgetAlt_Machine
import Definitions.Def_ForgetAlt_Supplement_MCM

namespace ForgetAlt.Supplement

open ForgetAlt

/-- **Theorem 5.1**, printed p.48 (PDF p.49). Izumi–Kitamura–Yamaguchi, *Forgetting Alternation
and Blossoms*, STOC 2027 submission (manuscript sha256 b656488c…).

"Given a matching system `I = (G, M)`, a maximal set of vertex-disjoint shortest augmenting paths
of `I` is computed in `O(m log n)` time. Consequently, an MCM of `G` is computed in
`O(m√n log n)` time."

**Formalization Note.** Algorithms are programs of the published word RAM `EndStatement`, time is
the number of steps, and a program must work at every width `W ≥ b·(⌊log₂ size⌋ + 1)` (the
conventions of the base mission's `ForgetAlt.Machine`). Clause 1: one program `B` outputs a
maximal set of vertex-disjoint shortest augmenting paths (`AugProblem true`) for every graph on
`Fin n` (isolated vertices allowed) with every matching, within `C·(m·⌊log₂ n⌋ + 1)` steps.
Clause 2: one program outputs a maximum-cardinality matching of every graph on `Fin n` within
`C·(m·⌊√n⌋·⌊log₂ n⌋ + 1)` steps (`⌊√n⌋ = Nat.sqrt n`, within a factor 2 of `√n` for `n ≥ 1`).
"`O(g)`" is read as `≤ C·(g + 1)`. -/
theorem theorem_5_1 :
    (∃ (B : List EndStatement.Instr) (b C : ℕ),
      AugRunsWithin true B b (fun n x => C * (x.edges.length * Nat.log 2 n + 1))) ∧
    (∃ (B : List EndStatement.Instr) (b C : ℕ),
      MCMRunsWithin B b (fun n x => C * (x.edges.length * Nat.sqrt n * Nat.log 2 n + 1))) := by sorry

end ForgetAlt.Supplement
