-- Prove2me | Theorems.Thm_ConvexOptAlg_Ellipsoid_cut_keeps_X
-- name    : ConvexOptAlg.Ellipsoid.cut_keeps_X
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:31:21.584976+00:00
-- url     : https://prove2.me/theorems/2c680022-aad7-4315-a914-56342c5d5e90
-- title:
--   Remark before Theorem 2.4, p. 250 — a point of X leaves E_t only if c_t ∈ X, and then its value exceeds f(c_t)
-- statement:
--   Let $n\ge2$, $R>0$, and let $(c_t,H_t,w_t)$ be a run of the ellipsoid method on $\mathcal X\subset\mathbb R^n$ with objective $f$, started from the Euclidean ball of center $c_0$ and radius $R$. Fix $t$ such that the oracle answers $w_0,\dots,w_t$ are all nonzero, and write $\mathcal E_s=\{x:(x-c_s)^\top H_s^{-1}(x-c_s)\le1\}$. If $x\in\mathcal X$ lies in $\mathcal E_t$ but not in $\mathcal E_{t+1}$, then
--
--   $$
--   c_t\in\mathcal X\qquad\text{and}\qquad f(c_t)<f(x).
--   $$
--
--   This is the ellipsoid-method analogue of (2.2) for the center of gravity method: a cut never removes a point of $\mathcal X$ unless it is a value cut at a center in $\mathcal X$, and such a cut removes only points that are worse than that center.
--
--   **Formalization Note** The page states only "at step $t$ one can remove a point in $\mathcal X$ from the current ellipsoid only if $c_t\in\mathcal X$"; the second conclusion is the inequality of (2.2) that "the exact same argument" of Theorem 2.1 uses. The nonzero answers guarantee that every $H_s$, $s\le t+1$, is a genuine update.
-- source:
--   Bubeck, arXiv:1405.4980v2, §2.2, remark before Theorem 2.4, p. 250; cf. (2.2), p. 246

import Mathlib
import Definitions.Def_ConvexOptAlg_Ellipsoid_Defs

namespace ConvexOptAlg.Ellipsoid

/-- The remark before Theorem 2.4 (Bubeck, arXiv:1405.4980v2, §2.2, p. 250): at step `t` of the
ellipsoid method a point of `X` can be removed from the current ellipsoid only if `c_t ∈ X`, and
then (as in (2.2), p. 246) its value exceeds `f(c_t)`. Formally: in a run with `n ≥ 2`, `R > 0`
and nonzero oracle answers `w_0, …, w_t`, every `x ∈ X` lying in `E_t` but not in `E_{t+1}`
satisfies `c_t ∈ X` and `f(c_t) < f(x)`, where
`E_s = {x : (x − c_s)⊤H_s⁻¹(x − c_s) ≤ 1}`. -/
theorem cut_keeps_X {n : ℕ} (hn : 2 ≤ n) (X : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (R : ℝ) (hR : 0 < R) (c0 : Fin n → ℝ) (c : ℕ → Fin n → ℝ)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (w : ℕ → Fin n → ℝ)
    (hrun : IsEllipsoidRun X f R c0 c H w) (t : ℕ) (hw : ∀ s ≤ t, w s ≠ 0)
    (x : Fin n → ℝ) (hxX : x ∈ X) (hxt : x ∈ LinearOptimization.ellipsoid (c t) (H t))
    (hxt1 : x ∉ LinearOptimization.ellipsoid (c (t + 1)) (H (t + 1))) :
    c t ∈ X ∧ f (c t) < f x := by sorry

end ConvexOptAlg.Ellipsoid
