-- Prove2me | Theorems.Thm_DirTeleMC_Supplement_theorem_1_3
-- name    : DirTeleMC.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:44:38.564322+00:00
-- url     : https://prove2.me/theorems/381d14f8-1123-42bc-afc3-2c145187d893
-- title:
--   Theorem 1.3 — on planar digraphs LPSEP computes a DTM schedule of length $O(\log^2 k)\,\mathrm{OPT}$ in polynomial time
-- statement:
--   Let LPSEP be run with $p=3$ and a separator algorithm for the planar graphs (Definition 5.1).
--
--   1. Such a separator algorithm exists: a deterministic polynomial-time algorithm that, for every connected planar graph $H$, vertex $r$, spanning tree $A$ of $H$ rooted at $r$ and nonnegative rational vertex weights $\mu$, returns a nonempty set $Z$ of at most three vertices such that every component of $H-A[r,Z]$ has weight at most $\mu(V(H))/2$.
--   2. There is an absolute constant $C$ such that, for every such separator algorithm, LPSEP is a deterministic polynomial-time algorithm that, given a planar digraph, a source $s$ and a set $K$ of $k\ge2$ terminals reachable from $s$ with $s\notin K$, returns a valid schedule $S$ informing all terminals with
--   $$|S|\le C\,(\log_2k)^2\,\mathrm{OPT}.$$
--
--   This extends the polylogarithmic approximation for directed telephone multicast to planar digraphs in polynomial time; it is the case $p=3$ of Theorem 5.2.
--
--   **Formalization Note** A digraph is planar when its underlying graph has a crossing-free drawing (published `WilliamsonShmoys.HasPlanarDrawingOn`). The machine computes, on every such instance, the output of some run of LPSEP; its running-time exponent may depend on the separator algorithm, the constant $C$ does not.
--
--   Differences from the source:
--   - reading: LPSEP run with the separator algorithm of Thorup [Tho04, Lemma 2.3] → LPSEP run with any separator algorithm Z for the planar class with p = 3 (IsClassAlgorithm 3 PlanarClass Z), together with the existence of one; reason: the paper cites and does not define Thorup's algorithm; by Lemmas C.12–C.13 it is a separator algorithm in this sense
--   - generalization: the bound for LPSEP with Thorup's algorithm → the bound for LPSEP with every separator algorithm for the planar class, with one constant C for all of them; reason: Thorup's algorithm is one of them (Lemma C.13), so the statement specializes to the source's
--   - encoding: O(log² k) OPT → C · (log₂ k)² · OPT with an absolute real C chosen before the separator algorithm and the instance; reason: standard reading of O(·); k ≥ 2 so log₂ k > 0
--   - encoding: planar digraph → the underlying graph (loops and parallel arcs dropped) has a crossing-free drawing, WilliamsonShmoys.HasPlanarDrawingOn; reason: the paper defines a planar digraph by its underlying graph (p.36)
--   - encoding: polynomial time (no machine model named) → Mathlib Turing.TM2ComputableInTime over Fin 4 with time at most (m + 2)^c on inputs of length m, inputs encInst, outputs encSched; reason: the encoding is of size polynomial in n (adjacency matrix), so the bounds agree
--   - encoding: LPSEP (Algorithms 4 and 5), with its free choices → the machine outputs a schedule S with LPSepRun p Z I S, every free choice open; reason: the source leaves instance orders, weights, BFS trees and ties open; every run is admitted
--   - encoding: OPT, the minimum number of rounds of a feasible schedule → comparison with every valid schedule that informs all terminals; reason: no minimum over a possibly empty set is taken; same instances and same bound
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Theorem 1.3, p.3 (PDF p.4); restated p.37 (PDF p.38); proof p.48 (PDF p.49); Lemmas C.12–C.13, p.48 (PDF p.49)

import Mathlib
import Definitions.Def_DirTeleMC_Schedule
import Definitions.Def_DirTeleMC_encInst
import Definitions.Def_DirTeleMC_Supplement_IsRootPathSeparable
import Definitions.Def_DirTeleMC_Supplement_IsClassAlgorithm
import Definitions.Def_DirTeleMC_Supplement_LPSepRun

namespace DirTeleMC.Supplement

open DirTeleMC OnlineCRS.Combine

/-- **Theorem 1.3** (LPSEP on planar digraphs).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Theorem 1.3, p.3 (restated p.37, proved p.48): "Given a planar digraph, a source s,
and a set of k ≥ 2 terminals reachable from s, LPSEP, run with the separator algorithm of Thorup [Tho04, Lemma 2.3],
deterministically computes a DTM schedule of length O(log² k) OPT in polynomial time."

1. There is a separator algorithm for the planar graphs with `p = 3` (Definition 5.1): a polynomial-time function
   that, for every connected planar graph, vertex `r`, spanning tree and nonnegative rational weights, returns a
   nonempty set of at most three vertices whose root paths leave components of at most half the weight.
2. There is an absolute constant `C` such that for every such separator algorithm `Z` there are a constant `c` and a
   function `alg`, computed by a Turing machine in time at most `(m + 2)^c` on inputs of length `m`, such that on every
   well-formed DTM instance (`k = |K|`) whose digraph is planar, the output of `alg` is a schedule `S` returned by a
   run of LPSEP with `p = 3` and `Z`, `S` is valid and informs all terminals, and `|S| ≤ C (log₂ k)² |S′|` for every
   valid schedule `S′` that informs all terminals.

**Formalization Note.** Planarity is that of the underlying graph, via the published
`WilliamsonShmoys.HasPlanarDrawingOn` (a crossing-free drawing in the plane). Thorup's algorithm, which the paper
cites and does not define, is one separator algorithm of part 1 (Lemmas C.12–C.13); part 2 is stated for every
separator algorithm, so it covers Thorup's. Machine model and OPT as in Theorem 5.2. -/
theorem theorem_1_3 :
    (∃ Z : SepInput → List ℕ, IsClassAlgorithm 3 PlanarClass Z) ∧
    ∃ C : ℝ, ∀ Z : SepInput → List ℕ, IsClassAlgorithm 3 PlanarClass Z →
      ∃ c : ℕ, ∃ alg : Inst → List (List (ℕ × ℕ)),
        (∃ M : Turing.TM2ComputableInTime encInst encSched alg, ∀ m, M.time m ≤ (m + 2) ^ c) ∧
        ∀ I : Inst, I.WF → I.k = I.K.card → PlanarClass I.n (underlying I.adj) →
          ∃ S : Schedule I.n, alg I = S.toNat ∧ LPSepRun 3 Z I S ∧ S.Valid I ∧ S.InformsK I ∧
            ∀ S' : Schedule I.n, S'.Valid I → S'.InformsK I →
              (S.length : ℝ) ≤ C * Real.logb 2 I.k ^ 2 * S'.length := by sorry

end DirTeleMC.Supplement
