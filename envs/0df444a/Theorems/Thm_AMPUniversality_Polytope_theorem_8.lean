-- Prove2me | Theorems.Thm_AMPUniversality_Polytope_theorem_8
-- name    : AMPUniversality.Polytope.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:36:44.154652+00:00
-- url     : https://prove2.me/theorems/e53d3809-3d1d-41f6-9acb-98e739ccf22d
-- title:
--   Theorem 8, pp. 39–40 — basis-pursuit success below and failure above ρ∗
-- statement:
--   Let $m(n)=\lfloor n\delta\rfloor$ with $\delta\in(0,1)$. Each $m(n)\times n$ matrix $A(n)=\widetilde A(n)+\nu_0G(n)$ has independent mean-zero entries of variance $1/m(n)$ and common sub-Gaussian scale $s/m(n)$; $\nu_0>0$, and $G(n)$ has independent $N(0,1/m(n))$ entries independent of $\widetilde A(n)$. Consider either an identically distributed entry law with a fixed deterministic signal sequence of limiting support ratio $\rho$, or a possibly nonidentical entry law with signals whose coordinates are independent and identically distributed, independent of $A(n)$, and nonzero with probability $\rho\delta$.
--
--   If $\alpha>0$ parameterizes the phase boundary by $f_\delta(\alpha)=\delta$, then
--
--   $$\rho<f_\rho(\alpha)\implies\Pr\{\ell^1\text{ recovery succeeds}\}\to1,\qquad\rho>f_\rho(\alpha)\implies\Pr\{\ell^1\text{ recovery succeeds}\}\to0.$$
--
--   This is the compressed-sensing transition used to derive the geometric result. **Formalization Note** The unit-variance convention of Theorem 2 is deliberately not used here; this theorem has variance $1/m(n)$ and a Gaussian component of the same variance.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, pp. 39–40, Theorem 8

import Mathlib
import Definitions.Def_AMPUniversality_Polytope_Curve
import Definitions.Def_AMPUniversality_Polytope_Recovery

set_option autoImplicit false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace AMPUniversality.Polytope

/-- Theorem 8, pp. 39–40: the basis-pursuit phase transition for both signal models. -/
theorem theorem_8 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (ρ α : ℝ) (hα : 0 < α) (hcurve : fδ α = δ)
    (Atil G : ∀ n, Ω → Matrix (Fin (rowCount δ n)) (Fin n) ℝ)
    (ν0 : ℝ) (hν : 0 < ν0) (s : ℝ≥0)
    (hG : HasGaussianComponent P (rowCount δ) Atil G
      (fun n => ((rowCount δ n : ℝ≥0)⁻¹)))
    (hA : RectangularMatrixLaw P (rowCount δ)
      (perturbedMatrix (rowCount δ) Atil G ν0)
      (fun n => ((rowCount δ n : ℝ)⁻¹))
      (fun n => s / (rowCount δ n : ℝ≥0)))
    (x0 : ∀ n, Ω → Fin n → ℝ)
    (hsignal : TheoremEightSignal P (rowCount δ)
      (perturbedMatrix (rowCount δ) Atil G ν0) x0 δ ρ) :
    (ρ < fρ α →
      Tendsto (fun n => P {ω | L1Succeeds
        (perturbedMatrix (rowCount δ) Atil G ν0 n ω) (x0 n ω)})
        atTop (𝓝 1)) ∧
    (ρ > fρ α →
      Tendsto (fun n => P {ω | L1Succeeds
        (perturbedMatrix (rowCount δ) Atil G ν0 n ω) (x0 n ω)})
        atTop (𝓝 0)) := by sorry

end AMPUniversality.Polytope
