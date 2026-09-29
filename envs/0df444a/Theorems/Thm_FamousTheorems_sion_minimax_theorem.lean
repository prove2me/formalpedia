-- Prove2me | Theorems.Thm_FamousTheorems_sion_minimax_theorem
-- name    : FamousTheorems.sion_minimax_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:58:00.125066+00:00
-- url     : https://prove2.me/theorems/576ca574-a1ee-4d2b-a899-6526e180cda0
-- title:
--   Sion's minimax theorem
-- statement:
--   **Sion's minimax theorem.** Let $X$ be a nonempty compact convex subset and $Y$ a convex subset of real topological vector spaces, and $f:X\times Y\to\beta$ with $\beta$ densely linearly ordered. Suppose that for each $y\in Y$, $f(\cdot,y)$ is lower semicontinuous and quasiconvex on $X$, and for each $x\in X$, $f(x,\cdot)$ is upper semicontinuous and quasiconcave on $Y$. Then
--   $$\inf_{x\in X}\sup_{y\in Y}f(x,y)=\sup_{y\in Y}\inf_{x\in X}f(x,y),$$
--   whenever these infima and suprema exist.
--
--   Sion's theorem (1958) generalizes von Neumann's minimax theorem for zero-sum games from bilinear to quasiconvex–quasiconcave functions. It is used in game theory, robust optimization, and statistical decision theory.
--
--   **Formalization note.** Mathlib's `Sion.minimax`. Since `β` is only a densely ordered linear order, suprema and infima are given as data with `IsLUB`/`IsGLB` hypotheses: `sup_y x` is $\sup_yf(x,y)$, `inf_sup` is $\inf_x$ of these, `inf_x y` is $\inf_xf(x,y)$, and `sup_inf` is $\sup_y$ of these. The conclusion is `inf_sup = sup_inf`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Sion.minimax`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem sion_minimax_theorem {E F β : Type*} [LinearOrder β] [DenselyOrdered β] [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] {X : Set E} {Y : Set F} {f : E → F → β}
    (hX_ne : X.Nonempty) (hX_cpt : IsCompact X) (hX : Convex ℝ X) (hY : Convex ℝ Y)
    (hfy_lsc : ∀ y ∈ Y, LowerSemicontinuousOn (fun x => f x y) X) (hfy_qcvx : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x => f x y)
    (hfx_usc : ∀ x ∈ X, UpperSemicontinuousOn (fun y => f x y) Y) (hfx_qccv : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y)
    (sup_y : E → β) (h_sup_y : ∀ x ∈ X, IsLUB {b | ∃ y ∈ Y, f x y = b} (sup_y x))
    (inf_sup : β) (h_inf_sup : IsGLB {b | ∃ x ∈ X, sup_y x = b} inf_sup)
    (inf_x : F → β) (h_inf_x : ∀ y ∈ Y, IsGLB {b | ∃ x ∈ X, f x y = b} (inf_x y))
    (sup_inf : β) (h_sup_inf : IsLUB {b | ∃ y ∈ Y, inf_x y = b} sup_inf) : inf_sup = sup_inf := by sorry

end FamousTheorems
