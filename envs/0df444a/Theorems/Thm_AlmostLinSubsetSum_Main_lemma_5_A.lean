-- Prove2me | Theorems.Thm_AlmostLinSubsetSum_Main_lemma_5_A
-- name    : AlmostLinSubsetSum.Main.lemma_5_A
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:29:40.264769+00:00
-- url     : https://prove2.me/theorems/c515ec0e-9c10-462c-9798-c0511aea187a
-- title:
--   Lemma 5.A — Macbeath overlap (Ewald–Larman–Rogers): overlapping $1/5$-Macbeath regions nest in the scale-$1$ region
-- statement:
--   **Lemma 5.A** (p. 21; [2, Lemma 2.2]). Let $K\subset\mathbb R^d$ be a convex body and let $p,y\in K$. If $M^{1/5}_K(p)\cap M^{1/5}_K(y)\ne\emptyset$, then $M^{1/5}_K(y)\subseteq M^1_K(p)$, where $M^\lambda_K(p)=p+\lambda\cdot\bigl((K-p)\cap(p-K)\bigr)$.
--
--   Differences from the source:
--   - encoding: convex body K ⊂ ℝ^d → IsConvexBody K: compact, convex, nonempty interior, in Fin d → ℝ; reason: the standard meaning of convex body
-- source:
--   Chen, Mao, Zhang (2026), An Almost-Linear Time Algorithm for Multidimensional Subset Sum, STOC 2027 submission, SHA-256 0cd42ca048cfff088013ad06450a278a6df72a29004c48c5c138f3f6df85d1e0, Lemma 5.A, p. 21

import Mathlib
import Definitions.Def_AlmostLinSubsetSum_Main_Basic
import Definitions.Def_AlmostLinSubsetSum_Main_Geometry

set_option autoImplicit false

namespace AlmostLinSubsetSum.Main

/-- **Lemma 5.A** (Macbeath overlap; Ewald–Larman–Rogers, cited in Chen, Mao, Zhang 2026,
p. 21). Let `K ⊂ ℝ^d` be a convex body and let `p, y ∈ K`. If
`M^{1/5}_K(p) ∩ M^{1/5}_K(y) ≠ ∅`, then `M^{1/5}_K(y) ⊆ M^1_K(p)`, where
`M^λ_K(p) := p + λ · ((K − p) ∩ (p − K))`. -/
theorem lemma_5_A {d : ℕ} (K : Set (Fin d → ℝ)) (hK : IsConvexBody K)
    (p y : Fin d → ℝ) (hp : p ∈ K) (hy : y ∈ K)
    (hmeet : (macbeathRegion K (1 / 5) p ∩ macbeathRegion K (1 / 5) y).Nonempty) :
    macbeathRegion K (1 / 5) y ⊆ macbeathRegion K 1 p := by sorry

end AlmostLinSubsetSum.Main
