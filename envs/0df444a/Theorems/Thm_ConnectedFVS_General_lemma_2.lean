-- Prove2me | Theorems.Thm_ConnectedFVS_General_lemma_2
-- name    : ConnectedFVS.General.lemma_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T17:18:23.46899+00:00
-- url     : https://prove2.me/theorems/37f634b3-3500-4591-ad2b-d6ea8b7a694c
-- title:
--   Lemma 2 — Directed Steiner Out-Tree in single-exponential time and polynomial space
-- statement:
--   There are one deterministic finite program $M$, positive constants $C,C_s$ and natural exponents $d,d_s$, all independent of the input, such that $M$ decides Directed Steiner Out-Tree. For every finite directed graph $D$, root $r$, terminal set $S$ and integer vertex budget $p$, write $l=|S|$ and $N$ for the length of its encoding. The actual run halts, accepts if and only if an out-tree rooted at $r$ contains every terminal and has at most $p$ vertices, and satisfies
--
--   $$T\le C\,2^l(N+1)^d,\qquad \mathrm{peakSpace}\le C_s(N+1)^{d_s}.$$
--
--   Both bounds apply to the same deterministic program and run. Empty terminal sets, roots in the terminal set, arbitrary ambient directed cycles and nonpositive budgets are included. This is an exact decision algorithm, including correct rejection.
--
--   Differences from the source:
--   - encoding: finite graphs with named vertices → vertices Fin n with explicit Boolean adjacency and membership matrices; reason: every finite input has a relabeling; no graph-class restriction is imposed
--   - encoding: input size n and integer tree budgets → self-delimiting binary encodings with signed tree budgets, length N, and rejection of malformed words; reason: matrix and membership encodings are polynomially related to explicit graph input size, and budget bit length is counted
--   - reading: tree and out-tree without a separate null-tree convention → trees are nonempty, so nonpositive vertex budgets are rejected and a rooted singleton is allowed; reason: the standard tree convention matches the distinguished root and the source definition of out-tree
--   - generalization: directed graph inputs under the usual loopless convention → the ambient directed adjacency matrix may also contain self-arcs; reason: self-arcs cannot occur in any out-tree, so deleting them recovers all source instances and preserves answers and polynomial input costs
--   - encoding: a deterministic algorithm with asymptotic resource bounds → one finite ordinary binary-stack program with globally quantified positive natural constants and exponents, exact step counts, and bounds using (N+1); reason: finite alphabets exclude unit-cost unbounded data; fixed-machine simulations and per-instance polynomial arithmetic costs preserve the claimed exponential base
--   - encoding: polynomial space → a uniform bound on live bits on all stacks plus finite control, including input, at every instant of the same timed run; reason: including a read-only input copy adds only N cells; the run history is not counted as retained storage
-- source:
--   Misra et al., FPT-Algorithms for Connected Feedback Vertex Set, arXiv:0909.3180v1 (17 September 2009), Lemma 2, PDF p. 5

import Definitions.Def_ConnectedFVS_General_BinaryMachine
import Definitions.Def_ConnectedFVS_General_Encodings

namespace ConnectedFVS.General

theorem lemma_2 :
    ∃ (M : BinaryMachine) (C d Cs ds : ℕ), 0 < C ∧ 0 < Cs ∧
      M.Decides dsotLanguage ∧ ∀ I : DSOTInstance,
        M.Bounded I.encode (C * 2 ^ I.terminals.card * (I.encode.length + 1) ^ d)
          (Cs * (I.encode.length + 1) ^ ds) := by sorry

end ConnectedFVS.General
