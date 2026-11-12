-- Prove2me | Theorems.Thm_FasterWCTFPTAS_Main_lemma_3_3
-- name    : FasterWCTFPTAS.Main.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:35.674208+00:00
-- url     : https://prove2.me/theorems/e00479ff-9df6-4367-95e5-71411947982f
-- title:
--   Lemma 3.3 — every δ/(2m)-kernel is a relaxed δ-representative set
-- statement:
--   Let $m\ge2$, $\delta\in(0,1)$, $A,B,X\ge0$, and let $D\subseteq[0,A]^{m-1}\times[0,B]\subseteq\mathbb R^m$ be a set of points. Then every $\varepsilon$-kernel $Q$ of $D$ with
--
--   $$
--   \varepsilon=\frac{\delta}{2m}
--   $$
--
--   is a relaxed $\delta$-representative set of $D$ for $(A,B,X)$.
--
--   This reduces the computation of relaxed representative sets to the computation of $\varepsilon$-kernels, for which near-optimal algorithms are known.
--
--   Differences from the source:
--   - generalization: width_v(S) = max − min of ⟨s, v/‖v‖⟩ over S (defined when the maximum and minimum exist) → supremum minus infimum, for every D in the box; reason: D and every Q ⊆ D are bounded (they lie in the box), and the supremum and infimum equal the maximum and minimum whenever these exist (in particular for finite D), so the statement specializes to the paper's on every D for which the paper's widths are defined
--   - encoding: ε-kernel defined through max/min of inner products → IsKernel additionally requires Q nonempty when S is nonempty; reason: the width of the empty set is undefined in the source; the condition excludes only that case
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, STOC 2027 submission #1072 (October 2026), p. 10 (PDF p. 11), Lemma 3.3

import Mathlib
import Definitions.Def_FasterWCTFPTAS_Main_Geometry

set_option autoImplicit false

namespace FasterWCTFPTAS.Main

/-- Lemma 3.3, p. 10 (PDF 11): let `m ≥ 2`, `δ ∈ (0, 1)`, `A, B, X ≥ 0` and
`D ⊆ [0, A]^{m−1} × [0, B] ⊆ ℝ^m`. Then every `ε`-kernel of `D` with `ε = δ/(2m)` is a relaxed
`δ`-representative set of `D` for `(A, B, X)`. The directional widths are suprema minus infima of
bounded sets (`D` lies in the box), which are the paper's maxima minus minima whenever these
exist, in particular for finite `D`. -/
theorem lemma_3_3 {m : ℕ} (hm : 2 ≤ m) (δ A B X : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hX : 0 ≤ X) (D : Set (Pt m))
    (hbox : ∀ s ∈ D, InBox A B s) (Q : Set (Pt m)) (hQ : IsKernel (δ / (2 * m)) Q D) :
    IsRelaxedRep δ A B X Q D := by sorry

end FasterWCTFPTAS.Main
