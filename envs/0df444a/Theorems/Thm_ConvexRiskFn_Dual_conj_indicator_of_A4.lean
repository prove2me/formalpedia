-- Prove2me | Theorems.Thm_ConvexRiskFn_Dual_conj_indicator_of_A4
-- name    : ConvexRiskFn.Dual.conj_indicator_of_A4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:34.35498+00:00
-- url     : https://prove2.me/theorems/9ad670a1-61ed-4c09-8ae6-f12e8a9bc966
-- title:
--   Proof of Theorem 2.2(iii), p. 436 — under (A4), ρ* is the indicator function of {μ ∈ 𝒴 : ⟨μ, ·⟩ ≤ ρ}
-- statement:
--   Let $(\mathcal X,\mathcal Y)$ be a paired system as in §2 and $\rho:\mathcal X\to\overline{\mathbb R}$ proper, lower semicontinuous, convex (A1) and positively homogeneous (A4): $\rho(tX)=t\rho(X)$ for $t>0$. Then for every $\mu\in\mathcal Y$
--   $$\rho^*(\mu)=\begin{cases}0,&\text{if }\langle\mu,X\rangle\le\rho(X)\text{ for all }X\in\mathcal X,\\ +\infty,&\text{otherwise,}\end{cases}$$
--   so $\rho^*$ is the indicator function of the set $\mathcal C=\{\mu\in\mathcal Y:\langle\mu,X\rangle\le\rho(X)\ \forall X\}$.
--
--   The paper states that $\rho^*$ is the indicator function of a closed convex subset of $\mathcal Y$. The set $\mathcal C$ is an intersection of half-spaces $\{\mu:\langle\mu,X\rangle\le\rho(X)\}$, each closed in any topology on $\mathcal Y$ compatible with the pairing, so $\mathcal C$ is closed and convex. Combined with (2.6), this gives the representation (2.7) of Theorem 2.2(iii).
--
--   **Formalization Note** The set is named explicitly instead of quantifying over an unspecified closed convex set; no topology on $\mathcal Y$ is introduced.
-- source:
--   Ruszczyński, Shapiro, Optimization of convex risk functions, Math. Oper. Res. 31 (2006), p. 436, proof of Theorem 2.2(iii)

import Mathlib
import Definitions.Def_ConvexRiskFn_Dual_Setting

namespace ConvexRiskFn.Dual

/-- Proof of Theorem 2.2(iii), p. 436: if a proper, lower semicontinuous, convex `ρ` is positively
homogeneous, then its conjugate is the indicator function of the set
`{μ ∈ 𝒴 : ⟨μ, X⟩ ≤ ρ(X) ∀ X ∈ 𝒳}` (value `0` on it, `+∞` off it). -/
theorem conj_indicator_of_A4 {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [AddCommGroup 𝒳] [Module ℝ 𝒳]
    [TopologicalSpace 𝒳] [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    (S : PairedSpaces Ω 𝒳) (ρ : 𝒳 → EReal) (hp : IsProper ρ)
    (hlsc : LowerSemicontinuous ρ) (hcvx : A1 ρ) (hA4 : A4 ρ) :
    ∀ μ ∈ S.Y,
      ((∀ X, ((pair μ (S.toFun X) : ℝ) : EReal) ≤ ρ X) → conj S ρ μ = 0) ∧
      ((¬ ∀ X, ((pair μ (S.toFun X) : ℝ) : EReal) ≤ ρ X) → conj S ρ μ = ⊤) := by sorry
end ConvexRiskFn.Dual
