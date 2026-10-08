-- Prove2me | Theorems.Thm_ConvexRiskFn_Dual_theorem_2_1
-- name    : ConvexRiskFn.Dual.theorem_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:01.426408+00:00
-- url     : https://prove2.me/theorems/a56f4723-cae1-4f71-bd02-f24a27d5d96b
-- title:
--   Theorem 2.1 (Fenchel–Moreau), p. 435 — ρ** = lsc(ρ) for convex proper ρ (with lsc(ρ) > −∞)
-- statement:
--   Let $(\mathcal X,\mathcal Y)$ be a paired system as in §2 and $\rho:\mathcal X\to\overline{\mathbb R}$ a convex (A1) and proper risk function whose lower semicontinuous hull $\operatorname{lsc}(\rho)(X)=\liminf_{Z\to X}\rho(Z)$ is $>-\infty$ at every point. Then the biconjugate equals the lower semicontinuous hull:
--   $$\rho^{**}(X)=\sup_{\mu\in\mathcal Y}\{\langle\mu,X\rangle-\rho^*(\mu)\}=\operatorname{lsc}(\rho)(X)\qquad\text{for all }X\in\mathcal X.$$
--
--   This is the Fenchel–Moreau theorem in the paired-space setting, cited in the paper (Rockafellar, Aubin–Ekeland) and used to derive the representation (2.5)–(2.6).
--
--   **Formalization Note** The hypothesis $\operatorname{lsc}(\rho)>-\infty$ is added. Without it the statement as printed fails in infinite dimension: for a closed proper subspace $L$, a discontinuous linear $\ell$ on $L$, and $\rho=\ell$ on $L$, $+\infty$ off $L$, one has $\operatorname{lsc}(\rho)=-\infty$ on $L$ and $+\infty$ off $L$, while $\rho^*\equiv+\infty$ and $\rho^{**}\equiv-\infty$. The cited sources state the theorem with the closure $\operatorname{cl}\rho$, which coincides with $\operatorname{lsc}(\rho)$ exactly when $\operatorname{lsc}(\rho)$ never takes the value $-\infty$.
-- source:
--   Ruszczyński, Shapiro, Optimization of convex risk functions, Math. Oper. Res. 31 (2006), p. 435, Theorem 2.1 (Fenchel–Moreau), citing Rockafellar [22, Theorem 5] and Aubin–Ekeland [2, Theorem 4.4.2]

import Mathlib
import Definitions.Def_ConvexRiskFn_Dual_Setting

namespace ConvexRiskFn.Dual

/-- Theorem 2.1 (Fenchel–Moreau), p. 435: for a convex proper `ρ : 𝒳 → ℝ̄` whose lower
semicontinuous hull never takes the value `−∞`, `ρ** = lsc(ρ)`. -/
theorem theorem_2_1 {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [AddCommGroup 𝒳] [Module ℝ 𝒳]
    [TopologicalSpace 𝒳] [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    (S : PairedSpaces Ω 𝒳) (ρ : 𝒳 → EReal) (hcvx : A1 ρ) (hp : IsProper ρ)
    (hlscp : ∀ X, ⊥ < lscHull ρ X) :
    biconj S ρ = lscHull ρ := by sorry
end ConvexRiskFn.Dual
