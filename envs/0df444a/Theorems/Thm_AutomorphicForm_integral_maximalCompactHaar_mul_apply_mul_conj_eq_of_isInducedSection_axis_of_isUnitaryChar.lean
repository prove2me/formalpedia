-- Prove2me | Theorems.Thm_AutomorphicForm_integral_maximalCompactHaar_mul_apply_mul_conj_eq_of_isInducedSection_axis_of_isUnitaryChar
-- name    : AutomorphicForm.integral_maximalCompactHaar_mul_apply_mul_conj_eq_of_isInducedSection_axis_of_isUnitaryChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/085fd517-c556-5e52-a863-ebfe1f5d3ff7
-- title:
--   Right-invariance of the K-pairing for axis induced sections
-- statement:
--   Let $K$ be a number field, and let $\alpha \colon (\mathbb{A}_K)^\times \to \mathbb{R}^\times$ be the homomorphism obtained from the distributive Haar character of the adele ring by pushing its $\mathbb{R}_{\ge 0}$-values into $\mathbb{R}$ and passing to units. Assume $\alpha(x) > 0$ for every idele $x$. Let $\mu, \nu \colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ be characters that are unitary in the sense of `IsUnitaryChar`, i.e. $\|\mu(x)\| = \|\nu(x)\| = 1$ for all $x$; let $t \in \mathbb{R}$, put $s = ti$, and let $\varphi, \psi \colon GL_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous functions that are induced sections for the pair of characters $\eta_1 = \mu \cdot \alpha^{\,s + 1/2}$ and $\eta_2 = \nu \cdot \alpha^{-(s + 1/2)}$ (the powers being `cpowChar`, the complex powers of the positive real $\alpha$), meaning that $\varphi(bg) = \eta_1(b_{11})\,\eta_2(b_{22})\,\varphi(g)$ for every $b$ in the adelic Borel subgroup (matrices with vanishing lower-left entry) and every $g$, and likewise for $\psi$. Then for every $g \in GL_2(\mathbb{A}_K)$, $$\int_{\mathbf{K}} \varphi(kg)\,\overline{\psi(kg)}\,dk = \int_{\mathbf{K}} \varphi(k)\,\overline{\psi(k)}\,dk,$$ the integrals being taken against the Haar measure `maximalCompactHaar K` on the subgroup `adelicMaximalCompact K` of elements whose finite part is integral and whose archimedean components are row-isometries.
--
--   This is the unitarity of the principal series on the unitary axis $\mathrm{Re}(s) = 0$, expressed in the compact model: the $\mathbf{K}$-pairing of two induced sections is unchanged by right translation of the argument. It feeds the comparison of right convolution with its adjoint for such sections, [`AutomorphicForm.integral_maximalCompactHaar_rightConv_mul_conj_eq_integral_mul_conj_rightConv_star_of_isInducedSection_axis`](thm.html#AutomorphicForm.integral_maximalCompactHaar_rightConv_mul_conj_eq_integral_mul_conj_rightConv_star_of_isInducedSection_axis).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_maximalCompactHaar_mul_apply_mul_conj_eq_of_isInducedSection_axis_of_isUnitaryChar.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm
open scoped NNReal ComplexConjugate

theorem AutomorphicForm.integral_maximalCompactHaar_mul_apply_mul_conj_eq_of_isInducedSection_axis_of_isUnitaryChar
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (t : ℝ) (φ ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : IsInducedSection (𝓞 K) K (etaFst μ α hα ((t : ℂ) * Complex.I)) (etaSnd ν α hα ((t : ℂ) * Complex.I)) φ)
      (_hψ : IsInducedSection (𝓞 K) K (etaFst μ α hα ((t : ℂ) * Complex.I)) (etaSnd ν α hα ((t : ℂ) * Complex.I)) ψ)
      (_hφc : Continuous φ) (_hψc : Continuous ψ)
      (g : AdelicGL2 (𝓞 K) K),
    ∫ k, φ ((k : AdelicGL2 (𝓞 K) K) * g) * conj (ψ ((k : AdelicGL2 (𝓞 K) K) * g)) ∂(maximalCompactHaar K) =
      ∫ k, φ (k : AdelicGL2 (𝓞 K) K) * conj (ψ (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by sorry
