-- Prove2me | Theorems.Thm_BrownianEnergyRep_theorem_2_1
-- name    : BrownianEnergyRep.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:03:38.373362+00:00
-- url     : https://prove2.me/theorems/ccff4bbc-18b9-4183-9e3f-e58c3405a4f7
-- title:
--   Theorem 2.1 — the heat kernel: existence, uniqueness, symmetry, convolution formula
-- statement:
--   Let $G$ be a compact connected matrix group, $\mathfrak g$ its Lie algebra with an $\mathrm{Ad}_G$-invariant inner product, and $dx$ a Haar measure. The left heat equation (2.1) has a fundamental solution $p_t$, unique for $t>0$. The heat semigroup $e^{t\Delta/2}$ on $L^2(G,dx)$ exists. For $t>0$, $p_t(x)=p_t(x^{-1})$ for all $x\in G$, and for $f\in L^2(G,dx)$,
--   $$
--   e^{t\Delta/2}f(x)=\int_Gp_t(x^{-1}h)f(h)\,dh=\int_Gp_t(h^{-1}x)f(h)\,dh\quad\text{for a.e. }x .
--   $$
--   The heat kernel gives the transition densities of Brownian motion on $G$.
--
--   Differences from the source:
--   - encoding: G a compact connected Lie subgroup of GL_n(ℝ), 𝔤 its tangent space at e, with an Ad_G-invariant inner product → a subgroup with CompactSpace and ConnectedSpace, and a MatrixLieAlgebra structure (E, incl, Ad, bracket); reason: a compact subgroup of GL_n(ℝ) is a closed Lie subgroup, and the structure is determined by 𝔤 and the inner product
--   - reading: "the fundamental solution" of (2.1) → existence, and uniqueness for t > 0, of p with IsHeatKernel; reason: the printed definite article needs uniqueness; the goal is ill-posed without it
--   - encoding: e^{tΔ/2} the semigroup of the closure of Δ/2 on L²(G,dx) → a strongly continuous symmetric contraction semigroup whose generator extends Δ/2 on C^∞(G); reason: Δ/2 is essentially self-adjoint, so the generator is the closure
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Theorem 2.1, p.2

import Mathlib
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra
import Definitions.Def_BrownianEnergyRep_IsHeatKernel
import Definitions.Def_BrownianEnergyRep_IsHeatSemigroup

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- Theorem 2.1 (arXiv:1511.07378v1, p.2): existence and uniqueness of the fundamental solution, `p_t(x) = p_t(x⁻¹)`,
and the convolution formulas for `e^{tΔ/2}`.

**Formalization Note** Uniqueness is the meaning of "the fundamental solution". Values at `t ≤ 0` are
unconstrained, so uniqueness is stated for `t > 0`. -/
theorem theorem_2_1 {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) [CompactSpace ↥G] [ConnectedSpace ↥G]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : MatrixLieAlgebra G E) (m : Measure ↥G) [m.IsHaarMeasure] :
    (∃ p, IsHeatKernel L m p ∧ ∀ q, IsHeatKernel L m q → ∀ t > 0, ∀ x, q t x = p t x) ∧
    (∃ S, IsHeatSemigroup L m S) ∧
    ∀ p, IsHeatKernel L m p → ∀ t > 0,
      (∀ x, p t x = p t x⁻¹) ∧
      ∀ S, IsHeatSemigroup L m S → ∀ f : Lp ℝ 2 m,
        (S t f : ↥G → ℝ) =ᵐ[m] (fun x => ∫ h, p t (x⁻¹ * h) * f h ∂m) ∧
        (S t f : ↥G → ℝ) =ᵐ[m] (fun x => ∫ h, p t (h⁻¹ * x) * f h ∂m) := by sorry

end BrownianEnergyRep
