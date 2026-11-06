-- Prove2me | Theorems.Thm_BinaryQueryLB_lemma_2_9_b
-- name    : BinaryQueryLB.lemma_2_9_b
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:48:13.284474+00:00
-- url     : https://prove2.me/theorems/e47c45e1-9104-4798-9fac-5d9d2ec8329f
-- title:
--   Lemma 2.9(b) — $\min_XF_W=-(MR/2)h_W$ and $f_W((\bar y/R)^\circ)+h_W\le\frac{2}{MR}(F_W(y)-\min_XF_W)$
-- statement:
--   Let $d\ge2$, $R,M>0$, $m=\lfloor d/2\rfloor$, $W\in\mathcal W$, $p_W$ the point of $K_W$ closest to the origin and $h_W=\|p_W\|_2$. Then
--   $$
--   \min_X F_W=-\frac{MR}{2}\,h_W,
--   $$
--   that is, this value is attained at a point of $X$ and is a lower bound of $F_W$ on $X$, and every $y\in X$ satisfies
--   $$
--   f_W\big((\bar y/R)^\circ\big)+h_W\le\frac{2}{MR}\Big(F_W(y)-\min_X F_W\Big).
--   $$
--
--   Differences from the source:
--   - encoding: m = ⌊d/2⌋ → m = d / 2 (natural-number division); reason: the same number
--   - encoding: p_W, the point of K_W closest to the origin, and h_W = ∥p_W∥₂ → every point p of K_W of least norm, with h_W = ‖p‖; reason: there is exactly one such point
--   - encoding: min_X F_W = −(MR/2)h_W → the value −(MR/2)‖p‖ is attained on X and is a lower bound on X; min_X F_W in the inequality is this value; reason: the meaning of an attained minimum
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Lemma 2.9(b), p.14

import Mathlib
import Definitions.Def_BinaryQueryLB_FW__386b32
import Definitions.Def_BinaryQueryLB_fW
import Definitions.Def_BinaryQueryLB_radialProj
import Definitions.Def_BinaryQueryLB_Wset
import Definitions.Def_BinaryQueryLB_Box
import Definitions.Def_BinaryQueryLB_KW
import Definitions.Def_BinaryQueryLB_IsMinNormPoint

namespace BinaryQueryLB

/-- **Lemma 2.9(b) (Box and ball).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Lemma 2.9(b), p.14: "For every `W ∈ 𝒲`: … (b)
`min_X F_W = −(MR/2) h_W`, and every `y ∈ X` satisfies
`f_W((ȳ/R)°) + h_W ≤ (2/(MR))(F_W(y) − min_X F_W)`".

Here `h_W = ∥p_W∥₂` for the point `p_W` of `K_W` closest to the origin.

**Formalization Note.** "`min_X F_W = −(MR/2)h_W`" is stated as: the value is attained at a point
of `X` and is a lower bound of `F_W` on `X`; `min_X F_W` in the inequality is replaced by this
value. `d ≥ 2`, `R, M > 0`, `m = d / 2`; every least-norm point `p` of `K_W` is allowed. -/
theorem lemma_2_9_b (d : ℕ) (hd : 2 ≤ d) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (W : Fin (d / 2) → EuclideanSpace ℝ (Fin (d / 2))) (hW : W ∈ Wset (d / 2))
    (p : PtSpace (d / 2)) (hp : IsMinNormPoint (KW W) p) :
    (∃ y ∈ Box d R, FW d R M W y = -(M * R / 2) * ‖p‖) ∧
      (∀ y ∈ Box d R, -(M * R / 2) * ‖p‖ ≤ FW d R M W y) ∧
      ∀ y ∈ Box d R, fW W (radialProj (R⁻¹ • ybar d y)) + ‖p‖ ≤
        2 / (M * R) * (FW d R M W y - (-(M * R / 2) * ‖p‖)) := by sorry

end BinaryQueryLB
