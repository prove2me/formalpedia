-- Prove2me | Theorems.Thm_CutwidthCircuitLB_lemma_4_1
-- name    : CutwidthCircuitLB.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:29:51.755293+00:00
-- url     : https://prove2.me/theorems/61b33fd5-ff7a-4fb0-9ee5-e87b07529c0a
-- title:
--   Lemma 4.1 — read-once programs for a $K$-rectangle disperser have $\ge |f^{-1}(1)|/K^2$ edges
-- statement:
--   Let $K > 1$ and let $f : \{0,1\}^n \to \{0,1\}$ be a $K$-rectangle disperser. Then every read-once program computing $f$ has at least
--   $$
--   \frac{|f^{-1}(1)|}{K^2}
--   $$
--   edges.
--
--   It converts the rectangle-disperser property of the hard function into an edge lower bound, the branching-program half of the circuit lower bound.
--
--   Differences from the source:
--   - encoding: f is a K-rectangle disperser (Definition 4.1 is stated for K > 1) → hypotheses 1 < K and IsRectangleDisperser K f (a predicate written for every real K); reason: Definition 4.1's standing assumption K > 1 made explicit
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Lemma 4.1, p.11 (with Definition 4.1, p.11)

import Mathlib
import Definitions.Def_CutwidthCircuitLB_ROBP
import Definitions.Def_CutwidthCircuitLB_ROBP_IsConsistentSegment
import Definitions.Def_CutwidthCircuitLB_ROBP_IsAcceptingPath
import Definitions.Def_CutwidthCircuitLB_ROBP_Accepts
import Definitions.Def_CutwidthCircuitLB_ROBP_Computes
import Definitions.Def_CutwidthCircuitLB_ROBP_numEdges
import Definitions.Def_CutwidthCircuitLB_rect
import Definitions.Def_CutwidthCircuitLB_IsRectangleDisperser

namespace CutwidthCircuitLB

/-- **Lemma 4.1** (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Lemma 4.1, p.11): if `f` is a `K`-rectangle disperser (`K > 1`, as in
Definition 4.1), then every read-once program computing `f` has at least `|f⁻¹(1)|/K²` edges. -/
theorem lemma_4_1 {n : ℕ} (K : ℝ) (hK : 1 < K) (f : (Fin n → Bool) → Bool)
    (hf : IsRectangleDisperser K f) (R : ROBP n) (hR : R.Computes f) :
    (({x : Fin n → Bool | f x = true}.ncard : ℕ) : ℝ) / K ^ 2 ≤ (R.numEdges : ℝ) := by sorry

end CutwidthCircuitLB
