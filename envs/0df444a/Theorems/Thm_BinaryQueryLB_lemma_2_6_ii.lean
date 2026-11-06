-- Prove2me | Theorems.Thm_BinaryQueryLB_lemma_2_6_ii
-- name    : BinaryQueryLB.lemma_2_6_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:48:33.730821+00:00
-- url     : https://prove2.me/theorems/19955e86-b98e-41f4-9358-0530075202b4
-- title:
--   Lemma 2.6(ii) — $g_W(y)\in\partial F_W(y)$ for every $y\in X$
-- statement:
--   Let $d\ge2$, $R,M>0$ and $W\in\mathcal W$. For every $y\in X=[-R,R]^d$, the canonical subgradient is a subgradient of $F_W$:
--   $$
--   g_W(y)\in\partial F_W(y),\quad\text{that is,}\quad F_W(y')-F_W(y)\ge\langle g_W(y),y'-y\rangle\ \text{for all }y'\in\mathbb R^d .
--   $$
--
--   Together with Lemma 2.6(i) and (iii), this makes the canonical chart $G_{\mathrm{can}}$ of Definition 2.7 a well-defined first-order chart.
--
--   Differences from the source:
--   - encoding: m = ⌊d/2⌋ → m = d / 2 (natural-number division); reason: the same number
--   - encoding: ∂F_W(y) → ShorNonsmooth.Subdiff.subdifferential Set.univ (F_W) y; reason: the global subdifferential of a convex function on ℝ^d
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Lemma 2.6(ii), p.13

import Mathlib
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential
import Definitions.Def_BinaryQueryLB_FW__386b32
import Definitions.Def_BinaryQueryLB_gW
import Definitions.Def_BinaryQueryLB_Wset
import Definitions.Def_BinaryQueryLB_Box

namespace BinaryQueryLB

/-- **Lemma 2.6(ii) (Chart).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Lemma 2.6(ii), p.13: "Let `W ∈ 𝒲`. … (ii) `g_W(y) ∈ ∂F_W(y)` for
every `y ∈ X`."

**Formalization Note.** `∂F_W(y)` is the global subdifferential
`ShorNonsmooth.Subdiff.subdifferential Set.univ (F_W) y` (platform definition 3f41475b). -/
theorem lemma_2_6_ii (d : ℕ) (hd : 2 ≤ d) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (W : Fin (d / 2) → EuclideanSpace ℝ (Fin (d / 2))) (hW : W ∈ Wset (d / 2)) :
    ∀ y ∈ Box d R, gW d R M W y ∈ ShorNonsmooth.Subdiff.subdifferential Set.univ (FW d R M W) y := by sorry

end BinaryQueryLB
