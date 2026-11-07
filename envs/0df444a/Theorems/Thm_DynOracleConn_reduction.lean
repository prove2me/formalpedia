-- Prove2me | Theorems.Thm_DynOracleConn_reduction
-- name    : DynOracleConn.reduction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:51:45.636202+00:00
-- url     : https://prove2.me/theorems/4e35aac1-b593-4cb4-a3a9-234c7aa8042f
-- title:
--   §3, p.19 and p.26 — a connectivity algorithm yields a PPHP algorithm with the same memory and at most as many probes
-- statement:
--   Fix an injection of the named vertices. There is a translation of deterministic matrix-model connectivity algorithms with state set $S$ into PPHP stream algorithms with the **same** state set such that, for every instance $X$ and query sequence $\mathcal I$, the stream $\sigma$ of §3.1.1 satisfies the following.
--
--   1. $\sigma$ is valid, keeps the graph a forest throughout, and has length $8d-1+2|\mathcal I|$.
--   2. For every algorithm $A$: the PPHP run of the translation is a fixed function of the run of $A$ on $\sigma$ (the function depends on $X$ and $\mathcal I$ only); if $A$ answers correctly after every update of $\sigma$, then the translation answers all queries of $\mathcal I$ correctly; and the translation makes at most as many PPHP probes as $A$ makes adjacency probes on $\sigma$.
--
--   This is the step that makes it sufficient to prove the lower bound for PPHP.
--
--   **Formalization Note** The terminals are the images of $s$ and $t$. The insertion phase becomes the preprocessing map, and its probes are not charged to the PPHP run. The factorization through a fixed function is what carries measurability of randomized runs over. $8d-1$ is natural-number subtraction, equal to $0$ for $d=0$, when the graph has no edges.
--
--   Differences from the source:
--   - encoding: [d] 1-based → Fin d, 0-based; reason: Lean convention; same instances
--   - generalization: d = ⌊(n−2)/8⌋ and one vertex layout → any injection e of the named vertices into Fin n; reason: the paper's layout is one such injection
--   - encoding: the same memory → the same state type S; reason: memory is |S| ≤ 2^B wherever used
--   - generalization: the sentence on p.19 names memory, probes and correctness → added clauses: validity, the forest property, the exact length, and the transcript factorization; reason: they contain the printed statement; Theorem 4's proof (p.26) uses them
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), §3, p.19; §3.1.2, p.21; final paragraph of §3, p.26

import Mathlib
import Definitions.Def_DynOracleConn_Gadget
import Definitions.Def_DynOracleConn_Oracles
import Definitions.Def_DynOracleConn_DetAlg

namespace DynOracleConn

/-- **§3, p.19 (made precise on p.26) — the reduction from PPHP.** Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), §3, p.19: "To reduce from
the PPHP problem to s-t connectivity we construct for every instance (π, z) of PPHP a graph
𝒢n(π, z) such that after inserting the edges of this graph, every query on the PPHP problem can be
answered using 1 insertion and 1 deletion in the graph and querying then whether the fixed vertices
s and t are connected. Moreover, every adjacency-matrix probe in this graph can be answered with at
most one oracle probe of PPHP. Hence, an algorithm for s-t connectivity yields an algorithm for PPHP
with the same memory and at most the same number of probes". p.26: "each adjacency probe of A is
answered by at most one probe P_X(i, j), and A is correct at all time steps only if correct_total
holds".

For every injection `e`, there is a translation `red` of deterministic matrix-model algorithms with
state type `S` into PPHP stream algorithms with the same state type such that, for every instance
`X` and query sequence `ℐ`, the stream `σ = hardSeq e X ℐ`
1. is valid, keeps the graph a forest throughout, and has length `8d − 1 + 2|ℐ|`;
2. and for every algorithm `A`: the PPHP transcript of `red A` is a fixed function `F` (depending on
   `e, X, ℐ` only) of the transcript of `A` on `σ`; if `A` answers correctly after every update of
   `σ` then `red A` answers all queries of `ℐ` correctly; and `red A` makes at most as many PPHP
   probes as `A` makes adjacency probes on `σ`.

**Formalization Note.** The terminals are `e s` and `e t`. The factorization through `F` is what
makes the translation preserve measurability of randomized runs. `8 * d - 1` is natural-number
subtraction (`0` for `d = 0`, when 𝒢ₙ has no edges). -/
theorem reduction {n d : ℕ} {S : Type} (e : GV d ↪ Fin n) :
    ∃ red : DetAlg n (Fin n × Fin n) Bool S → PPHPAlg d S,
      ∀ (X : PPHPInst d) (ℐ : List (Fin d)),
        PunctSketch.IsValidStream (hardSeq e X ℐ) ∧ ForestThroughout (hardSeq e X ℐ) ∧
        (hardSeq e X ℐ).length = 8 * d - 1 + 2 * ℐ.length ∧
        ∃ F : List (List ((Fin n × Fin n) × Bool) × Bool) →
            List (List ((Fin d × Fin d) × Option Bool) × Bool),
          ∀ A : DetAlg n (Fin n × Fin n) Bool S,
            (red A).transcript X ℐ = F (A.transcript matrixOracle (hardSeq e X ℐ)) ∧
            (A.AllCorrect matrixOracle (e GV.s) (e GV.t) (hardSeq e X ℐ) →
              (red A).correctTotal X ℐ) ∧
            (red A).Ltotal X ℐ ≤ A.totalCost matrixOracle (hardSeq e X ℐ) := by sorry

end DynOracleConn
