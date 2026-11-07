-- Prove2me | Theorems.Thm_CutwidthCircuitLB_lemma_2_2
-- name    : CutwidthCircuitLB.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:28:31.941192+00:00
-- url     : https://prove2.me/theorems/cca1d87b-2e81-43e7-a2cd-38ddecb2daed
-- title:
--   Lemma 2.2 (Counting Lemma) — at most $EK^2$ accepted inputs
-- statement:
--   Let $R$ be a read-once program with $E$ edges and let $K > 1$. If $R$ contains no vertex $v$ (in any layer) with $\min\{|P_v|, |Q_v|\} \ge K$, then $R$ accepts at most
--   $$
--   E\,K^2
--   $$
--   inputs.
--
--   This is the "bottleneck" property: a program in which every vertex has a thin side cannot accept many inputs unless it has many edges.
--
--   Differences from the source: none.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Lemma 2.2, p.7

import Mathlib
import Definitions.Def_CutwidthCircuitLB_ROBP
import Definitions.Def_CutwidthCircuitLB_ROBP_IsConsistentSegment
import Definitions.Def_CutwidthCircuitLB_ROBP_IsAcceptingPath
import Definitions.Def_CutwidthCircuitLB_ROBP_Accepts
import Definitions.Def_CutwidthCircuitLB_ROBP_numEdges
import Definitions.Def_CutwidthCircuitLB_ROBP_past
import Definitions.Def_CutwidthCircuitLB_ROBP_PSet
import Definitions.Def_CutwidthCircuitLB_ROBP_QSet

namespace CutwidthCircuitLB

/-- **Lemma 2.2 (Counting Lemma)** (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Lemma 2.2, p.7): let `R` be a read-once program with `E`
edges and let `K > 1`. If `R` contains no vertex `v` with `min{|P_v|, |Q_v|} ≥ K`, then `R` accepts
at most `E K²` inputs. -/
theorem lemma_2_2 {n : ℕ} (R : ROBP n) (K : ℝ) (hK : 1 < K)
    (hR : ∀ (i : Fin (R.len + 1)) (v : Fin (R.layerSize i)),
      ¬ (K ≤ ((R.PSet i v).ncard : ℝ) ∧ K ≤ ((R.QSet i v).ncard : ℝ))) :
    (({x : Fin n → Bool | R.Accepts x}.ncard : ℕ) : ℝ) ≤ (R.numEdges : ℝ) * K ^ 2 := by sorry

end CutwidthCircuitLB
