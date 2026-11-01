-- Prove2me | Theorems.Thm_ExactModKL_proposition_3_9
-- name    : ExactModKL.proposition_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:57:37.957528+00:00
-- url     : https://prove2.me/theorems/4cb5b6bf-3e75-433d-97c6-98b5944a2a42
-- title:
--   Proposition 3.9 — the exact modulus is the smallest concave desingularizing function (corrected: $\tilde\varphi\in\Phi_\eta$ iff every level in $(0,\eta)$ is reached)
-- statement:
--   Let $f:\mathbb R^n\to(-\infty,\infty]$ be proper and lower semicontinuous, let $\bar x\in\operatorname{dom}\partial f$ (the limiting subdifferential $\partial f(\bar x)$ is nonempty), let $U$ be a neighbourhood of $\bar x$ and $\eta\in(0,\infty]$. Let $\varphi\in\Phi_\eta$ be concave and suppose that $f$ has the generalized concave KL property at $\bar x$ with respect to $U$, $\eta$ and $\varphi$: for every $x\in U\cap[0<f-f(\bar x)<\eta]$,
--   $$
--   \varphi'_-\big(f(x)-f(\bar x)\big)\cdot\operatorname{dist}\big(0,\partial f(x)\big)\ge1 .
--   $$
--   Let $h(s)=\sup\{\operatorname{dist}^{-1}(0,\partial f(x)):x\in U\cap[0<f-f(\bar x)<\eta],\ s\le f(x)-f(\bar x)\}$ be the function of Definition 3.6. Let $\tilde\varphi(t)=\int_0^th(s)\,ds$ be the exact modulus of the generalized concave KL property of $f$ at $\bar x$ with respect to $U$ and $\eta$ (Definition 3.6). Then:
--
--   1. $\tilde\varphi$ is well defined: $h(s)<\infty$ for every $s\in(0,\eta)$ and $\int_0^th(s)\,ds<\infty$ for every $t\in[0,\eta)$;
--   2. $\tilde\varphi$ is concave on $[0,\eta)$, $\tilde\varphi(0)=0$, $\tilde\varphi$ is right-continuous at $0$ and nondecreasing on $[0,\eta)$;
--   3. $\tilde\varphi(t)\le\varphi(t)$ for every $t\in[0,\eta)$;
--   4. $\tilde\varphi$ satisfies inequality (7): $\tilde\varphi'_-(f(x)-f(\bar x))\cdot\operatorname{dist}(0,\partial f(x))\ge1$ for every $x\in U\cap[0<f-f(\bar x)<\eta]$;
--   5. for every $t\in[0,\eta)$,
--   $$
--   \tilde\varphi(t)=\inf\big\{\psi(t):\ \psi\in\Phi_\eta\text{ is a concave desingularizing function of }f\text{ at }\bar x\text{ with respect to }U\text{ and }\eta\big\};
--   $$
--   6. $\tilde\varphi\in\Phi_\eta$ if and only if every level $s\in(0,\eta)$ is reached: some $x\in U$ with $\partial f(x)\neq\emptyset$ satisfies $s\le f(x)-f(\bar x)<\eta$. In that case $f$ has the generalized concave KL property at $\bar x$ with respect to $U$, $\eta$ and $\tilde\varphi$, and $\tilde\varphi$ is the least concave desingularizing function.
--
--   This answers the question "what is the optimal concave desingularizing function?": whenever one exists, the exact modulus is the pointwise smallest, and the finite-length and rate bounds of KL-based convergence proofs are sharpest with it.
--
--   **Formalization Note** Values of $f$ are extended reals and $\eta$ may be $\infty$. $h$ and $\operatorname{dist}^{-1}$ take values in $[0,\infty]$ with $\sup\emptyset=0$, and inequality (7) is written as $1\le\tilde\varphi'_-(f(x)-f(\bar x))\|v\|$ for every $v\in\partial f(x)$. The infimum in item 5 is stated pointwise as a greatest lower bound. The printed statement asserts $\tilde\varphi\in\Phi_\eta$ unconditionally. That is false: for $f(x)=|x|$, $\bar x=0$, $U=(-1,1)$, $\eta=\infty$ and $\varphi(t)=t$ one gets $\tilde\varphi(t)=\min(t,1)$. Item 6 states exactly when it holds.
--
--   Differences from the source:
--   - correction: ϕ̃ is concave and belongs to Φ_η (proof, p.13), and f has the generalized concave KL property at x̄ with respect to U, η and ϕ̃ (requires ϕ̃ ∈ Φ_η) → unconditionally: ϕ̃ concave, ϕ̃(0) = 0, right-continuous at 0, nondecreasing, and ϕ̃ satisfies (7); and ϕ̃ ∈ Φ_η if and only if every s ∈ (0, η) is reached by some x ∈ U with ∂f(x) ≠ ∅ and s ≤ f(x) − f(x̄) < η; reason: false as printed: f(x) = |x| on ℝ (proper, lsc, convex), x̄ = 0 (∂f(0) = [−1, 1]), U = (−1, 1), η = ∞, ϕ(t) = t (concave, in Φ_∞, (7) holds since ∂f(x) = {sign x} for x ≠ 0) give h = 1 on (0, 1) and h = sup ∅ on [1, ∞), so ϕ̃(t) = min(t, 1) is not strictly increasing; under the reachability condition the statement is the printed one
--   - reading: ϕ̃ = inf{ϕ ∈ Φ_η : ϕ is a concave desingularizing function of f at x̄ with respect to U and η} → for every t ∈ [0, η), ϕ̃(t) is the greatest lower bound (IsGLB) of {ψ(t) : ψ concave on [0, η), ψ ∈ Φ_η, ψ satisfies (7)}; reason: the infimum of functions is pointwise on their common domain [0, η); IsGLB does not presuppose that ϕ̃ belongs to the set, which fails when the reachability condition fails (correction above)
--   - reading: ϕ̃ is well-defined → h(s) < ∞ for s ∈ (0, η) and ∫⁻_{(0,t]} h < ∞ for t ∈ [0, η); reason: Definition 3.6 defines ϕ̃ under the assumption h(s) < ∞, as an ℝ₊-valued function, which needs the integral finite; the proof (p.13) shows both
--   - generalization: U ⊆ dom ∂f a neighborhood of x̄ (Definition 3.6) → U any neighbourhood of x̄ (U ∈ 𝓝 x̄); reason: points of U outside dom ∂f contribute ∞⁻¹ = 0 to h and satisfy (7) vacuously, so they change neither h nor the property; for U ⊆ dom ∂f the statement is the source's
--   - generalization: ℝⁿ with n ∈ ℕ = {1, 2, 3, …} (p.2) → n : ℕ, so n = 0 is included; reason: at n = 0 the space is a point, the band is empty, h = 0 and every clause holds; restricting to n ≥ 1 gives the source's statement
--   - encoding: dist(0, ∂f(x)) ∈ [0, ∞] with dist(0, ∅) = ∞; dist⁻¹; h(s) a supremum; inequality (7) ϕ′_−(f(x) − f(x̄))·dist(0, ∂f(x)) ≥ 1 → dist0 = Metric.infEDist 0 (∂f x) : ℝ≥0∞; its inverse in ℝ≥0∞; hfun a ⨆ in ℝ≥0∞ (sup ∅ = 0); (7) as ∀ v ∈ ∂f x, 1 ≤ ϕ′_−(f x − f x̄) · ‖v‖; real quantities compared with h through ENNReal.ofReal; reason: for ϕ′_− > 0 (every concave ϕ ∈ Φ_η, Lemma 3.1(ii)) the ∀ v form is the printed inequality with dist(0, ∅) = ∞, and a point with ∂f(x) = ∅ adds nothing to h; the same instances
--   - encoding: f : ℝⁿ → (−∞, ∞] proper lsc; x̄ ∈ dom ∂f; a nonempty neighborhood U of x̄; η ∈ (0, ∞]; ϕ̃ : [0, η) → ℝ₊ an integral; ϕ′_− → f : EuclideanSpace ℝ (Fin n) → EReal with IsProperFn f and LowerSemicontinuous f; (LimitingSubdiff f x̄).Nonempty; U ∈ 𝓝 x̄; η : ℝ≥0∞ with 0 < η; ϕ̃ = toReal of the lintegral of hfun over (0, t]; ϕ′_− = derivWithin · (Set.Iio t) t; ϕ, ψ : ℝ → ℝ constrained only on Ieta η; reason: Lean conventions; the same instances (η = ∞ is kept, the toReal is lossless by clause 1)
-- source:
--   Wang–Wang, arXiv:2008.13257v5, Proposition 3.9, p.12 (proof p.13)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_ExactModKL_Ieta
import Definitions.Def_ExactModKL_leftDeriv
import Definitions.Def_ExactModKL_PhiClass
import Definitions.Def_ExactModKL_KLIneq
import Definitions.Def_ExactModKL_dist0
import Definitions.Def_ExactModKL_hfun
import Definitions.Def_ExactModKL_exactModulus

open scoped ENNReal
open MeasureTheory Filter Topology

namespace ExactModKL

open NonconvexSplitting.Shared

/-- Proposition 3.9 (Wang–Wang, arXiv:2008.13257v5 (preprint), p.12), corrected. Let
`f : ℝⁿ → (−∞, ∞]` be proper lsc, `x̄ ∈ dom ∂f`, `U` a neighbourhood of `x̄`, `η ∈ (0, ∞]`,
and `ϕ ∈ Φ_η` concave such that `f` has the generalized concave KL property at `x̄` with respect
to `U`, `η` and `ϕ`. Then the exact modulus `ϕ̃` is well defined (`h < ∞` on `(0, η)` and
`∫_0^t h < ∞` on `[0, η)`), concave, `ϕ̃(0) = 0`, right-continuous at `0` and increasing,
`ϕ̃ ≤ ϕ` on `[0, η)`, `ϕ̃` satisfies inequality (7), `ϕ̃(t)` is for each `t ∈ [0, η)` the infimum
of `ψ(t)` over all concave desingularizing `ψ ∈ Φ_η`, and `ϕ̃ ∈ Φ_η` if and only if every level
`s ∈ (0, η)` is reached by some `x ∈ U ∩ dom ∂f` with `s ≤ f(x) − f(x̄) < η`.

**Formalization Note.** The printed statement claims `ϕ̃ ∈ Φ_η` unconditionally, which fails
(`f = |x|`, `x̄ = 0`, `U = (−1, 1)`, `η = ∞`, `ϕ(t) = t` gives `ϕ̃(t) = min(t, 1)`); the iff
states exactly when it holds, and under its right side the theorem is the printed one.
Conventions: `f` is `EReal`-valued, `η : ℝ≥0∞`, `h` and `dist⁻¹` are `ℝ≥0∞`-valued with
`sup ∅ = 0`, `ϕ̃` is the `toReal` of a lintegral proved finite, `ϕ′_−` is
`derivWithin ϕ (Set.Iio t) t`, inequality (7) is `∀ v ∈ ∂f x, 1 ≤ ϕ′_−(f x − f x̄)‖v‖`, the
infimum is pointwise (`IsGLB`), and `U` need not lie in `dom ∂f`. -/
theorem proposition_3_9 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hf : IsProperFn f)
    (hlsc : LowerSemicontinuous f) (xbar : EuclideanSpace ℝ (Fin n))
    (hxbar : (LimitingSubdiff f xbar).Nonempty) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : U ∈ 𝓝 xbar) (η : ℝ≥0∞) (hη : 0 < η)
    (ϕ : ℝ → ℝ) (hconc : ConcaveOn ℝ (Ieta η) ϕ) (hϕ : PhiClass η ϕ)
    (hKL : KLIneq f xbar U η ϕ) :
    (∀ s : ℝ, 0 < s → ENNReal.ofReal s < η → hfun f xbar U η s < ⊤) ∧
      (∀ t ∈ Ieta η, ∫⁻ s in Set.Ioc 0 t, hfun f xbar U η s < ⊤) ∧
      ConcaveOn ℝ (Ieta η) (exactModulus f xbar U η) ∧
      (exactModulus f xbar U η 0 = 0 ∧
        ContinuousWithinAt (exactModulus f xbar U η) (Set.Ici 0) 0 ∧
        MonotoneOn (exactModulus f xbar U η) (Ieta η)) ∧
      (∀ t ∈ Ieta η, exactModulus f xbar U η t ≤ ϕ t) ∧
      KLIneq f xbar U η (exactModulus f xbar U η) ∧
      (∀ t ∈ Ieta η, IsGLB {r : ℝ | ∃ ψ : ℝ → ℝ, ConcaveOn ℝ (Ieta η) ψ ∧ PhiClass η ψ ∧
          KLIneq f xbar U η ψ ∧ r = ψ t} (exactModulus f xbar U η t)) ∧
      (PhiClass η (exactModulus f xbar U η) ↔
        ∀ s : ℝ, 0 < s → ENNReal.ofReal s < η →
          ∃ x ∈ U, (LimitingSubdiff f x).Nonempty ∧ (s : EReal) ≤ f x - f xbar ∧
            f x - f xbar < (η : EReal)) := by sorry

end ExactModKL
