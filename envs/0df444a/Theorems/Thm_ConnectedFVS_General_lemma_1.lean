-- Prove2me | Theorems.Thm_ConnectedFVS_General_lemma_1
-- name    : ConnectedFVS.General.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T17:18:26.341696+00:00
-- url     : https://prove2.me/theorems/1f891146-b8d9-4662-80e4-8c59ecf6fefa
-- title:
--   Lemma 1 — GST Turing-reduces to Directed Steiner Out-Tree
-- statement:
--   Let $L_{\mathrm{GST}}$ be the decision language of finite undirected graphs with pairwise disjoint groups and an integer vertex budget, and let $L_{\mathrm{DSOT}}$ be the decision language of finite directed graphs with a root, a terminal set and an integer vertex budget, under the stated encodings. Then
--
--   $$L_{\mathrm{GST}}\le_T L_{\mathrm{DSOT}}$$
--
--   by a polynomial-time, parameter-preserving Turing reduction: there are one finite oracle program $M$, a positive constant $C$ and a natural exponent $d$, all independent of the input, such that, whenever the oracle answers membership in $L_{\mathrm{DSOT}}$ correctly, $M$ halts on every word and accepts exactly $L_{\mathrm{GST}}$; on the encoding (of length $N$) of every GST instance with $l$ groups it halts within $C(N+1)^d$ steps, each oracle answer costing one step; and every oracle query made on that run that encodes a Directed Steiner Out-Tree instance has at most $l$ terminals.
--
--   Differences from the source:
--
--   Differences from the source:
--   - encoding: finite graphs with named vertices → vertices Fin n with explicit Boolean adjacency and membership matrices; reason: every finite input has a relabeling; no graph-class restriction is imposed
--   - encoding: input size n and integer tree budgets → self-delimiting binary encodings with signed tree budgets, length N, and rejection of malformed words; reason: matrix and membership encodings are polynomially related to explicit graph input size, and budget bit length is counted
--   - reading: tree and out-tree without a separate null-tree convention → trees are nonempty, so nonpositive vertex budgets are rejected and a rooted singleton is allowed; reason: the standard tree convention matches the distinguished root and the source definition of out-tree
--   - generalization: directed graph inputs under the usual loopless convention → the ambient directed adjacency matrix may also contain self-arcs; reason: self-arcs cannot occur in any out-tree, so deleting them recovers all source instances and preserves answers and polynomial input costs
--   - encoding: Turing reducibility → a finite binary-stack oracle program, quantified before all input words; reason: push/pop/jump instructions implement ordinary effective computation; only the target language has an oracle instruction
--   - generalization: Turing-reduces, in the parameterized setting of §2 (an oracle algorithm whose running time and query parameters are bounded in terms of l and the input size, as the derivation "Lemmas 1 and 2 together imply Lemma 3" requires) → the oracle program halts within C(N+1)^d steps on every encoded GST instance and every query encoding a Directed Steiner Out-Tree instance has at most l terminals; reason: the proof's construction makes at most |V|+l queries, each a polynomial-size instance with exactly l terminals, so it gives this bound; it specializes to an fpt Turing reduction and to plain Turing reducibility, which alone would be trivial between two decidable languages
-- source:
--   Misra et al., FPT-Algorithms for Connected Feedback Vertex Set, arXiv:0909.3180v1 (17 September 2009), Lemma 1, PDF p. 4

import Definitions.Def_ConnectedFVS_General_BinaryMachine
import Definitions.Def_ConnectedFVS_General_Encodings

namespace ConnectedFVS.General

theorem lemma_1 :
    ∃ (M : BinaryMachine) (C d : ℕ), 0 < C ∧
      ∀ oracle : List Bool → Bool, (∀ w, oracle w = true ↔ dsotLanguage w) →
        M.DecidesWith oracle gstLanguage ∧ ∀ I : GSTInstance,
          M.HaltsWithin oracle I.encode (C * (I.encode.length + 1) ^ d) ∧
          ∀ (t : ℕ) (q : List Bool), M.queryWord (M.run oracle I.encode t) = some q →
            ∀ J : DSOTInstance, J.encode = q → J.terminals.card ≤ I.groups := by sorry

end ConnectedFVS.General
