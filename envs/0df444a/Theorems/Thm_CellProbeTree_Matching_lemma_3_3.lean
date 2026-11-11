-- Prove2me | Theorems.Thm_CellProbeTree_Matching_lemma_3_3
-- name    : CellProbeTree.Matching.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:35:40.685994+00:00
-- url     : https://prove2.me/theorems/47d545f0-b65d-46c1-88d2-5b5c5c0a5bd2
-- title:
--   Lemma 3.3 — actual-path discrepancy
-- statement:
--   Fix a deterministic, fully adaptive query algorithm: for every header $P$ and physical query $q$ a probe tree over the $s$ cells of $w$ bits. Let $(P, M_1)$ and $(P, M_2)$ be two valid states with the **same header** $P$ (the algorithm answers every physical query correctly on both), and suppose their correct answers to a physical query $q$ differ. Then some cell $c$ on the actual execution path of $q$ on the first state has different contents in the second:
--   $$\exists\, c \in \mathrm{path}(P, q, M_1) : \; M_1(c) \ne M_2(c).$$
--
--   Differences from the source:
--   - generalization: "two valid states" of the §3 experiment → any two states with the same header on which the algorithm answers every physical query according to a common specification; reason: the lemma uses only exactness, and the paper's valid states are such states, so the Lean statement specializes to the paper's.
--   - encoding: the actual ordinary execution path → the addresses of `ProbeTree.transcript (alg P q) M₁`; reason: Lean representation of the run.
-- source:
--   Liang, Liu, Nearly Tight Cell-Probe Lower Bounds for Querying on Tree via Talagrand Inequality, STOC 2027 submission (manuscript sha256 0e5a8eb2…), p. 12, Lemma 3.3

import Mathlib
import Definitions.Def_DynOracleConn_ProbeTree
import Definitions.Def_CellProbeTree_Matching_Execution

namespace CellProbeTree.Matching

open DynOracleConn

/-- Lemma 3.3 (actual-path discrepancy): if two valid states `(P, M₁)`, `(P, M₂)` with the same
header have different correct answers to a physical query `q`, some cell on the actual execution
path of `q` on the first state has different contents in the second. -/
theorem lemma_3_3 {s w : ℕ} {Hdr Qry Ans : Type}
    (alg : Hdr → Qry → ProbeTree (Fin s) (BitVec w) Ans)
    (spec : Hdr → (Fin s → BitVec w) → Qry → Ans)
    (P : Hdr) (M₁ M₂ : Fin s → BitVec w)
    (h₁ : IsValidState alg spec P M₁) (h₂ : IsValidState alg spec P M₂)
    (q : Qry) (hq : spec P M₁ q ≠ spec P M₂ q) :
    ∃ c ∈ actualPath alg P q M₁, M₁ c ≠ M₂ c := by sorry

end CellProbeTree.Matching
