-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_positive_radial_hessian_completion
-- name    : BirkhoffGlobalSection.positive_radial_hessian_completion
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T16:47:49.603823+00:00
-- url     : https://prove2.me/theorems/7467caf1-ef17-48cf-bbaa-0c7d3dd9dea8
-- title:
--   Positive radial completion of a tangential Hessian
-- statement:
--   Let $E$ be a real vector space, $B$ a symmetric bilinear form, $\ell:E\to\mathbb R$ a linear functional, and $x\in E$. Assume $r=\ell(x)>0$ and that $B$ is positive on every nonzero vector in $\ker\ell$. There is a symmetric positive definite bilinear form $S$ satisfying $S(x,w)=\ell(w)$, agreeing with $B$ on $\ker\ell\times\ker\ell$, and, more precisely,
--
--   $$
--   S(v,w)=B\!\left(v-\frac{\ell(v)}r x,w-\frac{\ell(w)}r x\right)+\frac{\ell(v)\ell(w)}r.
--   $$
--
--   For $\ell(v)=0$, this gives
--
--   $$S(v,w)=B(v,w)-\frac{B(v,x)}r\ell(w).$$
--
--   In the local strictly convex star-shaped Hamiltonian setting, take $\ell=dH(x)$ and $B=D^2H(x)$. The formula replaces the tangent Hessian by a fully positive form whose Hamiltonian linear system has the radial vector as a solution. On tangent directions its change is a shear along the Hamiltonian direction, so it preserves transverse quotient data. This is an elementary derived helper for the local index-bound frontier, not a claim that the winding estimate or the Birkhoff conjecture has been proved.
-- source:
--   Derived elementary bilinear-form completion for the local convexity argument underlying Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), Theorem 3.4 and equations (3.33)–(3.39), https://doi.org/10.2307/120994. Context: BirkhoffGlobalSection.dynamically_convex_on_strictly_convex_star_shaped_points; Liu–Salomao Proposition 1.11, https://arxiv.org/html/2506.17867v2. The displayed completion formula and its proof are supplied here as a derived lemma, not a verbatim numbered statement.

import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Data.Real.Basic

theorem BirkhoffGlobalSection.positive_radial_hessian_completion {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (ell : E →ₗ[ℝ] ℝ) (x : E)
    (hr : 0 < ell x) (hBsym : ∀ v w, B v w = B w v)
    (hBpos : ∀ v : E, ell v = 0 → v ≠ 0 → 0 < B v v) :
    ∃ S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ,
      (∀ v w, S v w = S w v) ∧
      (∀ v : E, v ≠ 0 → 0 < S v v) ∧
      (∀ w, S x w = ell w) ∧
      (∀ v w, ell v = 0 → S v w = B v w - (B v x / ell x) * ell w) ∧
      (∀ v w, S v w =
        B (v - (ell v / ell x) • x) (w - (ell w / ell x) • x) +
          ell v * ell w / ell x) := by sorry
