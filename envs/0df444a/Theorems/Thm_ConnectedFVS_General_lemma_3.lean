-- Prove2me | Theorems.Thm_ConnectedFVS_General_lemma_3
-- name    : ConnectedFVS.General.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T17:18:22.556131+00:00
-- url     : https://prove2.me/theorems/01417cb7-61b9-4e77-8dad-b06d18c10efc
-- title:
--   Lemma 3 — Group Steiner Tree in single-exponential time and polynomial space
-- statement:
--   There are one deterministic finite program $M$, positive constants $C,C_s$ and natural exponents $d,d_s$, independent of the input, such that $M$ decides Group Steiner Tree. For every finite simple undirected graph $G$, $l$ pairwise vertex-disjoint groups and integer budget $p$, let $N$ be its encoding length. The actual run halts, accepts if and only if a nonempty tree subgraph on at most $p$ vertices meets every group, and satisfies
--
--   $$T\le C\,2^l(N+1)^d,\qquad \mathrm{peakSpace}\le C_s(N+1)^{d_s}.$$
--
--   The tree is not required to be induced and may meet a group more than once. Empty input graphs, empty groups, zero groups and nonpositive budgets are included. Correct rejection and both resource bounds concern this same deterministic program.
--
--   Differences from the source:
--   - encoding: finite graphs with named vertices → vertices Fin n with explicit Boolean adjacency and membership matrices; reason: every finite input has a relabeling; no graph-class restriction is imposed
--   - encoding: input size n and integer tree budgets → self-delimiting binary encodings with signed tree budgets, length N, and rejection of malformed words; reason: matrix and membership encodings are polynomially related to explicit graph input size, and budget bit length is counted
--   - reading: tree and out-tree without a separate null-tree convention → trees are nonempty, so nonpositive vertex budgets are rejected and a rooted singleton is allowed; reason: the standard tree convention matches the distinguished root and the source definition of out-tree
--   - encoding: a deterministic algorithm with asymptotic resource bounds → one finite ordinary binary-stack program with globally quantified positive natural constants and exponents, exact step counts, and bounds using (N+1); reason: finite alphabets exclude unit-cost unbounded data; fixed-machine simulations and per-instance polynomial arithmetic costs preserve the claimed exponential base
--   - encoding: polynomial space → a uniform bound on live bits on all stacks plus finite control, including input, at every instant of the same timed run; reason: including a read-only input copy adds only N cells; the run history is not counted as retained storage
-- source:
--   Misra et al., FPT-Algorithms for Connected Feedback Vertex Set, arXiv:0909.3180v1 (17 September 2009), Lemma 3, PDF p. 5

import Definitions.Def_ConnectedFVS_General_BinaryMachine
import Definitions.Def_ConnectedFVS_General_Encodings

namespace ConnectedFVS.General

theorem lemma_3 :
    ∃ (M : BinaryMachine) (C d Cs ds : ℕ), 0 < C ∧ 0 < Cs ∧
      M.Decides gstLanguage ∧ ∀ I : GSTInstance,
        M.Bounded I.encode (C * 2 ^ I.groups * (I.encode.length + 1) ^ d)
          (Cs * (I.encode.length + 1) ^ ds) := by sorry

end ConnectedFVS.General
