-- Prove2me | Theorems.Thm_DetTerminalEmbedding1373_Real_Supplement_claim_7_3
-- name    : DetTerminalEmbedding1373.Real.Supplement.claim_7_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T08:16:32.727386+00:00
-- url     : https://prove2.me/theorems/fe7be7f8-62ec-4e6d-92a4-4dc82d786deb
-- title:
--   Claim 7.3 — convex-hull distortion is stable under perturbation of the vertices
-- statement:
--   Let $J$ be a finite index set, let $y_j,\hat y_j\in\mathbb R^d$ for $j\in J$, and let $\theta\ge 0$ with $\|y_j-\hat y_j\|\le\theta$ for every $j\in J$. Put $Y=\{y_j:j\in J\}$ and $\hat Y=\{\hat y_j:j\in J\}$. Then for every linear map $A:\mathbb R^d\to\mathbb R^m$,
--
--   $$\mathrm{chd}_Y(A)\le\mathrm{chd}_{\hat Y}(A)+\bigl(\|A\|_{\mathrm{op}}+1\bigr)\theta,$$
--
--   where $\mathrm{chd}$ is the convex hull distortion of Definition 7.2 and $\|A\|_{\mathrm{op}}$ is the operator norm with respect to the Euclidean norms.
--
--   In the paper this moves the convex-hull guarantee of the signing step from the rational approximations $\hat Y_k$ of the terminal directions to the exact directions $Y_k$ (Corollary 7.5).
--
--   Differences from the source:
--   - encoding: θ unconstrained → hypothesis 0 ≤ θ; reason: for nonempty J it follows from ‖y_j − ŷ_j‖ ≤ θ, and for J = ∅ it only excludes a negative θ, where the source's supremum over the empty hull is undefined
--   - encoding: sup over conv(Y) → Lean real supremum over the subtype convexHull ℝ (range y), which is 0 for an empty family; reason: for finite nonempty Y the hull is compact and the supremum is the source's maximum
--   - encoding: ‖A‖_op of a linear map → norm of LinearMap.toContinuousLinearMap A; reason: every linear map between finite-dimensional spaces is continuous and this is the Euclidean operator norm
-- source:
--   Vladimir Braverman, Kuan Cheng, Jiaqing Zhu, STOC 2027 submission #1373 (October 2026), p. 24, Claim 7.3 (with Definition 7.2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1373.pdf

import Mathlib
import Definitions.Def_DetTerminalEmbedding1373_Real_Supplement_chd

set_option autoImplicit false

namespace DetTerminalEmbedding1373.Real.Supplement

/-- Claim 7.3, p. 24. `Y = {y_j : j ∈ J}` and `Ŷ = {ŷ_j : j ∈ J}` share the finite index set `J`,
and `‖y_j - ŷ_j‖ ≤ θ` for every `j`. The operator norm is that of `A` as a continuous linear map.
`0 ≤ θ` only matters for `J = ∅` (otherwise it follows from the pairing bound). -/
theorem claim_7_3 {d m : ℕ} {J : Type} [Finite J] (y yhat : J → E d) (θ : ℝ)
    (A : E d →ₗ[ℝ] E m) (hθ : 0 ≤ θ) (hy : ∀ j, ‖y j - yhat j‖ ≤ θ) :
    chd A (Set.range y) ≤
      chd A (Set.range yhat) + (‖LinearMap.toContinuousLinearMap A‖ + 1) * θ := by sorry

end DetTerminalEmbedding1373.Real.Supplement
