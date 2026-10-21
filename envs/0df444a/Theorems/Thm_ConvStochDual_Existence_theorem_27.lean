-- Prove2me | Theorems.Thm_ConvStochDual_Existence_theorem_27
-- name    : ConvStochDual.Existence.theorem_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:54.903308+00:00
-- url     : https://prove2.me/theorems/66fe84de-0055-4e23-823e-ce75004a470a
-- title:
--   Theorem 27, p. 20 — no gap, dual attainment and scenario-wise optimality
-- statement:
--   For the paper's convex stochastic program, assume Assumption 23 and that $\operatorname{pos}(\operatorname{dom}\varphi-(0,\bar u))$ is closed and linear. Then
--
--   $$\inf(SP)=\inf(SP_{\mathcal X})=\sup(D),$$
--
--   and the ordinary dual optimum is attained. A feasible adapted strategy $x$ with finite objective solves $(SP)$ precisely when there is a dual feasible $(p,y)\in\mathcal X_a^\perp\times\mathcal Y$ such that $(p(\omega),y(\omega))\in\partial f(x(\omega),\bar u(\omega),\omega)$ almost surely.
--
--   The theorem transfers dual attainment to random-variable multipliers and gives pointwise optimality conditions for the original program over all adapted measurable strategies.
--
--   **Formalization Note** The printed second “inf (SP)” is read as “inf $(SP_{\mathcal X})$”. $Ef$ is also assumed proper and strongly lower semicontinuous, as required by Theorem 18. For the implication from primal optimality to a pointwise subgradient, $Ef(x,\bar u)>-\infty$ is required; the source's unqualified claim fails for an unbounded-below optimal strategy.
-- source:
--   Pennanen & Perkkiö, Dual solutions in convex stochastic optimization, arXiv:2205.15825v1, p. 20, Theorem 27

import Mathlib
import Definitions.Def_ConvStochDual_Existence_Setting

open MeasureTheory

namespace ConvStochDual.Existence

variable {Ω X U : Type*} [MeasurableSpace Ω]
  [AddCommGroup X] [Module ℝ X] [UniformSpace X]
  [IsUniformAddGroup X] [ContinuousSMul ℝ X]
  [AddCommGroup U] [Module ℝ U] [UniformSpace U]
  [IsUniformAddGroup U] [ContinuousSMul ℝ U]
  {T n m : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {τ : Fin n → Fin (T + 1)}
  {𝔽 : Fin (T + 1) → MeasurableSpace Ω}
  {ιX : X →ₗ[ℝ] RV Ω P n} {ιU : U →ₗ[ℝ] RV Ω P m}
  {V : Submodule ℝ (RV Ω P n)} {Y : Submodule ℝ (RV Ω P m)}

/-- Pennanen–Perkkiö, arXiv:2205.15825v1, p. 20, Theorem 27.
The printed second `(SP)` is read as `(SP_X)`; the forward optimality
implication requires the disclosed finite-below hypothesis. -/
theorem theorem_27 (s : Setting P τ 𝔽 ιX ιU V Y)
    (hS : Standing s) (hEf : EfProperLsc s) (hEt : CondExpClosed s)
    (hpos : LinClosed (pos ((fun q : X × U => q - (0, s.ubar)) '' domPhi s)))
    (hA23 : Assumption23_1 s ∧ Assumption23_2 s) :
    valSP s = valSPX s ∧ valSPX s = valD s ∧
    (∃ p : V, p ∈ XaPerp s ∧ ∃ y : Y, dualObj s p y = valD s) ∧
    (∀ x : RV Ω P n, Adapted τ 𝔽 P x → Ef s x (ιU s.ubar) < ⊤ →
      ((Ef s x (ιU s.ubar) ≠ ⊥ ∧
          ∀ x' : RV Ω P n, Adapted τ 𝔽 P x' → Ef s x (ιU s.ubar) ≤ Ef s x' (ιU s.ubar)) →
        ∃ p : V, p ∈ XaPerp s ∧ ∃ y : Y,
          ∀ᵐ ω ∂P, IsSubgradAt (s.f ω) (x ω) (ιU s.ubar ω)
            (p.1 ω) (y.1 ω)) ∧
      ((∃ p : V, p ∈ XaPerp s ∧ ∃ y : Y,
          ∀ᵐ ω ∂P, IsSubgradAt (s.f ω) (x ω) (ιU s.ubar ω)
            (p.1 ω) (y.1 ω)) →
        ∀ x' : RV Ω P n, Adapted τ 𝔽 P x' → Ef s x (ιU s.ubar) ≤ Ef s x' (ιU s.ubar))) := by sorry

end ConvStochDual.Existence
