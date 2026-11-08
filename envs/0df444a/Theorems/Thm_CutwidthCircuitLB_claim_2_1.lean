-- Prove2me | Theorems.Thm_CutwidthCircuitLB_claim_2_1
-- name    : CutwidthCircuitLB.claim_2_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T07:29:32.063208+00:00
-- url     : https://prove2.me/theorems/93124e71-5c0d-4318-bb02-d30fd99a46d5
-- title:
--   Claim 2.1 — $P_v \times Q_v$ is an accepting rectangle
-- statement:
--   Let $R$ be a read-once program computing $f : \{0,1\}^n \to \{0,1\}$, and let $v \in V_i$ be a vertex. Then $P_v \times Q_v$ is an **accepting rectangle** for $f$ with respect to the partition of the variables into the past and the future of $V_i$: $f(x) = 1$ for every input $x$ with
--   $$
--   x|_{\mathrm{past}(V_i)} \in P_v \quad\text{and}\quad x|_{\mathrm{future}(V_i)} \in Q_v .
--   $$
--
--   This is the rectangle structure of oblivious read-once programs that drives both the Counting Lemma 2.2 and Lemma 4.1.
--
--   Differences from the source: none.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Claim 2.1, p.7

import Mathlib
import Definitions.Def_CutwidthCircuitLB_ROBP
import Definitions.Def_CutwidthCircuitLB_ROBP_IsConsistentSegment
import Definitions.Def_CutwidthCircuitLB_ROBP_IsAcceptingPath
import Definitions.Def_CutwidthCircuitLB_ROBP_Accepts
import Definitions.Def_CutwidthCircuitLB_ROBP_Computes
import Definitions.Def_CutwidthCircuitLB_ROBP_past
import Definitions.Def_CutwidthCircuitLB_ROBP_PSet
import Definitions.Def_CutwidthCircuitLB_ROBP_QSet
import Definitions.Def_CutwidthCircuitLB_rect

namespace CutwidthCircuitLB

/-- **Claim 2.1** (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Claim 2.1, p.7): if a read-once program computes `f` and `v ∈ V_i`, then
`P_v × Q_v` is an accepting rectangle for `f` with respect to the partition of the variables into
the past and the future of `V_i`: `f = 1` on every input whose past part lies in `P_v` and whose
future part lies in `Q_v`. -/
theorem claim_2_1 {n : ℕ} (R : ROBP n) (f : (Fin n → Bool) → Bool) (hf : R.Computes f)
    (i : Fin (R.len + 1)) (v : Fin (R.layerSize i)) (x : Fin n → Bool)
    (hx : x ∈ rect (R.past i) (R.PSet i v) (R.QSet i v)) :
    f x = true := by sorry

end CutwidthCircuitLB
