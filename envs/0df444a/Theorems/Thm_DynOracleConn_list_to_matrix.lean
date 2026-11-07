-- Prove2me | Theorems.Thm_DynOracleConn_list_to_matrix
-- name    : DynOracleConn.list_to_matrix
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:49:52.1772+00:00
-- url     : https://prove2.me/theorems/ce8ede9e-ec2e-4054-950d-30f385d942b3
-- title:
--   p.26 (with p.15) — each adjacency-list probe is simulated by $n$ adjacency-matrix probes
-- statement:
--   There is a translation of list-model dynamic algorithms into matrix-model dynamic algorithms with the same state set such that, for every update sequence $\sigma$:
--
--   1. the matrix transcript of the translated algorithm is a fixed function of the list transcript of the original (the function depends on $\sigma$ only);
--   2. the answers agree;
--   3. the translated algorithm makes at most $n$ times as many probes.
--
--   A list-model bound for $BT\le cn$ is then the matrix-model bound for $B(nT)\le cn^2$.
--
--   **Formalization Note** The factorization in item 1 is what carries measurability of randomized runs over. The list oracle lists neighbors in increasing order.
--
--   Differences from the source:
--   - generalization: each probe is simulated by n probes → an added clause: the matrix transcript is a function of the list transcript, for fixed σ; reason: it contains the printed statement; it is needed to transfer measurable runs
--   - generalization: the neighbors are listed in an arbitrary order → increasing order; reason: an algorithm for arbitrary orders works in particular for this one
--   - encoding: Neighbor(v, j) undefined outside [d(v)] → returns 0; reason: an out-of-range query carries no information beyond d(v)
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), final remark of §3, p.26; §2, p.15

import Mathlib
import Definitions.Def_DynOracleConn_Oracles
import Definitions.Def_DynOracleConn_DetAlg

namespace DynOracleConn

/-- **p.26 (with p.15) — list probes by matrix probes.** Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), p.26: "Note that the lower bound of the
adjacency-list model holds since every probe of the adjacency-list model can be simulated by n
probes of the adjacency matrix model." §2, p.15: "each query of the list model can be simulated by
n queries of the matrix model".

There is a translation `sim` of list-model algorithms into matrix-model algorithms with the same
state type such that, for every update sequence `σ`: the matrix transcript of `sim A` is a fixed
function `F` (depending on `σ` only) of the list transcript of `A`; the answers agree; and `sim A`
makes at most `n` times as many probes.

**Formalization Note.** The list oracle lists neighbors in increasing order (`listOracle`). The
factorization through `F` is what transfers measurability of randomized runs. -/
theorem list_to_matrix {n : ℕ} {S : Type} :
    ∃ sim : DetAlg n (ListQuery n) ℕ S → DetAlg n (Fin n × Fin n) Bool S,
      ∀ σ : List (PunctSketch.Update n),
        ∃ F : List (List (ListQuery n × ℕ) × Bool) → List (List ((Fin n × Fin n) × Bool) × Bool),
          ∀ A : DetAlg n (ListQuery n) ℕ S,
            (sim A).transcript matrixOracle σ = F (A.transcript listOracle σ) ∧
            (sim A).answers matrixOracle σ = A.answers listOracle σ ∧
            (sim A).totalCost matrixOracle σ ≤ n * A.totalCost listOracle σ := by sorry

end DynOracleConn
