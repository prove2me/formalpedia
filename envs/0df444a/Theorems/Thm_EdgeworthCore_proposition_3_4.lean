-- Prove2me | Theorems.Thm_EdgeworthCore_proposition_3_4
-- name    : EdgeworthCore.proposition_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:14:37.425986+00:00
-- url     : https://prove2.me/theorems/6fee938b-893d-4f9e-92a0-c59c0e0ec03f
-- title:
--   Proposition 3.4 — a positive directional derivative gives a step $\mu\in(0,1]$ that does not decrease a $C^1$ concave function
-- statement:
--   Let $C\subseteq\mathbb R^\ell$ be convex and let $u$ be continuously differentiable and concave on $C$. Let $x,w\in C$ satisfy
--   $$\nabla u(x)^{\mathsf T}x<\nabla u(x)^{\mathsf T}w .$$
--   Then there is $\mu\in(0,1]$ such that
--   $$u(x)\le u\big((1-\mu)x+\mu w\big).$$
--
--   In the paper this is the ascent step used in the proof of Lemma 3.3 to move a trade vector toward $(-\delta)\mathbf 1$ without leaving the upper contour set.
--
--   **Formalization Note** $\nabla u(x)$ is the derivative of $u$ within $C$ at $x$, and $\nabla u(x)^{\mathsf T}v$ is that derivative applied to $v$. Bundles are `EuclideanSpace ℝ (Fin ℓ)`.
--
--   Differences from the source:
--   - generalization: u : ℝ^ℓ → ℝ continuously differentiable and concave, x, w ∈ ℝ^ℓ → u continuously differentiable and concave on a convex set C ∋ x, w, gradient taken within C; reason: for C = ℝ^ℓ this is the page's statement (the derivative within ℝ^ℓ is the derivative); the general form applies to utilities defined on ℝ^ℓ_+ as in Lemma 3.3
--   - encoding: ℝ^ℓ → EuclideanSpace ℝ (Fin ℓ); reason: Lean convention, same instances
-- source:
--   Barman–Echenique, arXiv:1905.05165v1, §3.1, Proposition 3.4, p.11 (proof pp.11–12)

import Mathlib
import Definitions.Def_EdgeworthCore_Model

namespace EdgeworthCore

/-- **Proposition 3.4** (Barman–Echenique, arXiv:1905.05165v1, §3.1, p.11). For a continuously
differentiable and concave function `u`, let `x, w` satisfy `∇u(x)ᵀx < ∇u(x)ᵀw`. Then there is
`μ ∈ (0, 1]` with `u(x) ≤ u((1 − μ)x + μw)`.

**Formalization Note.** The page states this for `u : ℝ^ℓ → ℝ`. Here `u` is continuously
differentiable and concave on a convex set `C ⊆ ℝ^ℓ` containing `x` and `w`, and `∇u(x)` is the
derivative within `C` (`fderivWithin`), applied to a vector `v` for `∇u(x)ᵀv`. For `C = ℝ^ℓ`
this is the page's statement (`fderivWithin_univ`); the general form is what the proof of
Lemma 3.3 needs for utilities defined on `ℝ^ℓ_+`. -/
theorem proposition_3_4 {ℓ : ℕ} (C : Set (Bundle ℓ)) (hC : Convex ℝ C) (u : Bundle ℓ → ℝ)
    (hu : ContDiffOn ℝ 1 u C) (hconc : ConcaveOn ℝ C u) (x w : Bundle ℓ) (hx : x ∈ C)
    (hw : w ∈ C) (hgrad : fderivWithin ℝ u C x x < fderivWithin ℝ u C x w) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 ∧ u x ≤ u ((1 - μ) • x + μ • w) := by sorry

end EdgeworthCore
