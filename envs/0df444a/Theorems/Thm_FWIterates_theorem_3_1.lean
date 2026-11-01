-- Prove2me | Theorems.Thm_FWIterates_theorem_3_1
-- name    : FWIterates.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:25:11.169475+00:00
-- url     : https://prove2.me/theorems/a8cbb4bf-11c1-482c-b922-7f50a620ed1e
-- title:
--   Theorem 3.1 — smooth convex interpolation of nested polygonal sketches with prescribed gradient directions (corrected: directions in the interior of the normal cone, one direction per vertex)
-- statement:
--   Let $(\mathcal P_\ell)_{\ell\in\mathbb N}$ be polytopes in $\mathbb R^2$, $(u_k)_{k\in\mathbb N}$ unit vectors, $(V_k)_{k\in\mathbb N}$ vertices of the polytopes and $(\delta_\ell)_{\ell\in\mathbb N}\in\,]0,1[^{\mathbb N}$ such that
--
--   1. (i) for every $k$ there is $\ell$ with $V_k\in\operatorname{vert}\mathcal P_\ell$ and $u_k$ in the cone of admissible directions $\mathcal K_{\mathcal P_\ell}V_k$ and in the interior of the normal cone $\mathcal N_{\mathcal P_\ell}V_k$;
--   2. a vertex carries one direction: $V_k=V_{k'}\Rightarrow u_k=u_{k'}$;
--   3. (ii) $\lambda\mathcal P_{\ell+1}\subset\operatorname{int}\mathcal P_\ell$ for all $\ell$ and $\lambda\in[1-\delta_\ell,1+\delta_\ell]$;
--   4. (iii) $0\in\operatorname{int}\mathcal P_\ell$ for all $\ell$.
--
--   Then for every open convex $\mathcal D\subset\mathbb R^2$ with $\mathcal P_0\subset\mathcal D$ and every integer $d\ge2$ there exist a $d$-times continuously differentiable convex $f:\mathcal D\to\mathbb R$ and $(\eta_\ell)\in\mathbb R^{\mathbb N}$ with, for all $k,\ell$,
--   $$
--   \eta_{\ell+1}<\eta_\ell,\qquad \mathcal P_\ell\subset\mathcal L_\ell,\qquad f|_{\operatorname{vert}\mathcal P_\ell}=\eta_\ell,\qquad \operatorname{dist}(\mathcal P_\ell,\mathcal L_\ell)\le\delta_\ell,
--   $$
--   where $\mathcal L_\ell=\{x\in\mathcal D\mid f(x)\le\eta_\ell\}$; moreover $\mathcal L_\ell$ has positive curvature, $\nabla f(V_k)$ is a positive multiple of $u_k$, $\operatorname{arg\,min}_{\mathcal D}f=\bigcap_\ell\mathcal P_\ell$, and $\nabla^2f$ is positive definite on $\mathcal D\setminus\bigcap_\ell\mathcal P_\ell$.
--
--   The paper quotes this theorem from Bolte–Pauwels [1]; it builds a convex function, as smooth as desired, from polygonal sketches and lets one prescribe its gradient directions at the vertices. All counterexamples of the paper are built with it.
--
--   Differences from the source:
--
--   - correction: (i) for all k there exists ℓ such that u_k ∈ K_{P_ℓ}V_k → u_k ∈ K_{P_ℓ}V_k and u_k ∈ int N_{P_ℓ}V_k, with V_k ∈ vert P_ℓ; reason: the printed theorem is false: P_ℓ = (1 + 2^{−ℓ})[−1, 1]², δ_ℓ = 2^{−ℓ−3}, V_k = (2, 2), u_k = e₁ satisfy (i)–(iii), but (ix), convexity and (v) force f ≡ η₀ on the edge {2} × [−2, 2], against (x) at (2, 0) ∉ ⋂P_ℓ = [−1, 1]²; the same argument refutes every u_k on the boundary of N_{P_ℓ}V_k, so the condition is necessary
--   - correction: no condition on repeated vertices in (V_k) → V_k = V_{k'} → u_k = u_{k'}; reason: the printed theorem is false: with the squares above, V₀ = V₁ = (2, 2), u₀ = (1, 2)/√5 and u₁ = (2, 1)/√5 (both in the interior of the quadrant K) satisfy (i)–(iii), but (ix) would need ∇f(V₀) positively colinear to two different unit vectors
--   - reading: (viii) {x | f(x) ⩽ η_ℓ} has positive curvature → at every x ∈ D with f(x) = η_ℓ, ∇f(x) ≠ 0 and ∇²f(x)(τ, τ) > 0 for every τ ≠ 0 with ⟨τ, ∇f(x)⟩ = 0; reason: for a C² function this is positive curvature τᵀ∇²fτ/‖∇f‖ of the level curve that bounds the sublevel set
--   - reading: (x) ∇²f is positive definite outside of arg min_D f = ⋂_ℓ P_ℓ → two clauses: {x ∈ D | ∀ y ∈ D, f x ≤ f y} = ⋂_ℓ P_ℓ, and fderiv ℝ (fderiv ℝ f) x h h > 0 for x ∈ D \ ⋂_ℓ P_ℓ and h ≠ 0; reason: the equality is a claim of the theorem, not notation
--   - encoding: f : D → ℝ → f : ℝ² → ℝ with every property (convexity, smoothness, sublevel sets, gradient, Hessian) required on D only; reason: the values of f outside D never enter; D is open, so gradients and Hessians at points of D are the true ones
--   - encoding: sublevel sets {x ∈ ℝ² | f(x) ⩽ η_ℓ} → {x | x ∈ D ∧ f x ≤ η ℓ}; reason: f is only defined on D
--   - encoding: dist(P_ℓ, {f ⩽ η_ℓ}) ⩽ δ_ℓ (Hausdorff distance, §2.1) → IsCompact {…} and Metric.hausdorffEDist (P ℓ) {…} ≤ ENNReal.ofReal (δ ℓ); reason: §2.1 defines dist for two nonempty compact sets only, so the page's (vii) includes compactness of the sublevel set (nonempty by (v)); the extended distance has no junk value
--   - encoding: polytopes, vert P, (u_k) ∈ S^ℕ, ∇²f → convex hulls of finite sets, Set.extremePoints ℝ, ‖u k‖ = 1, fderiv ℝ (fderiv ℝ f); reason: standard Lean renderings of the same objects
-- source:
--   Bolte, Combettes & Pauwels, The Iterates of the Frank-Wolfe Algorithm May Not Converge, arXiv:2202.08711v1, Theorem 3.1, p.4 (quoted from J. Bolte and E. Pauwels, Curiosities and counterexamples in smooth convex optimization, Math. Program. 2022)

import Mathlib
import Definitions.Def_FWIterates_IsSketch
import Definitions.Def_FWIterates_IsInterpolant

open scoped RealInnerProductSpace

namespace FWIterates

/-- **Theorem 3.1** (arXiv:2202.08711v1, Theorem 3.1, p.4, quoted from Bolte–Pauwels [1]),
*corrected*. Let `(P ℓ)` be polytopes of `ℝ²`, `(u k)` unit vectors, `(V k)` vertices of the
polytopes and `(δ ℓ) ∈ ]0, 1[^ℕ` satisfying hypotheses (i)–(iii) with the corrections of
`IsSketch` (`u k` also in the interior of the normal cone; one direction per vertex). Then for every
open convex `D ⊂ ℝ²` with `P 0 ⊆ D` and every `d ≥ 2` there are a `d`-times continuously
differentiable convex `f : D → ℝ` and levels `(η ℓ)` satisfying (iv)–(x) (`IsInterpolant`).

**Formalization Note** See `IsSketch` for the two corrections and their counterexample, and
`IsInterpolant` for the readings of (vii), (viii) and (x). -/
theorem theorem_3_1 (P : ℕ → Set (EuclideanSpace ℝ (Fin 2)))
    (V u : ℕ → EuclideanSpace ℝ (Fin 2)) (δ : ℕ → ℝ) (hS : IsSketch P V u δ)
    (D : Set (EuclideanSpace ℝ (Fin 2))) (hD : IsOpen D) (hDc : Convex ℝ D) (hPD : P 0 ⊆ D)
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ (f : EuclideanSpace ℝ (Fin 2) → ℝ) (η : ℕ → ℝ), IsInterpolant D d P V u δ f η := by sorry

end FWIterates
