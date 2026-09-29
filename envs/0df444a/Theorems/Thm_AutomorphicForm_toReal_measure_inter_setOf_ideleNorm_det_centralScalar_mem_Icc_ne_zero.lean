-- Prove2me | Theorems.Thm_AutomorphicForm_toReal_measure_inter_setOf_ideleNorm_det_centralScalar_mem_Icc_ne_zero
-- name    : AutomorphicForm.toReal_measure_inter_setOf_ideleNorm_det_centralScalar_mem_Icc_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/00270ace-58a7-592b-95c7-a67dae23e86d
-- title:
--   Nonvanishing Haar mass of a norm band of idele classes
-- statement:
--   Let $K$ be a number field and let $\alpha,\beta$ be real numbers with $0<\alpha$ and $\alpha<\beta$. Fix a measurable structure on the unit group $(\mathbb{A}_K)^\times$ of the adele ring of $K$ which is the Borel structure of its topology, let $\nu$ be a Haar measure on $(\mathbb{A}_K)^\times$, and let $\Omega \subseteq (\mathbb{A}_K)^\times$ be a fundamental domain, in the sense of `MeasureTheory.IsFundamentalDomain` for $\nu$, for the action of the image of $K^\times$ in $(\mathbb{A}_K)^\times$ under the unit-group map induced by the structure morphism $K \to \mathbb{A}_K$. Consider the subset of $z \in \Omega$ such that the quantity $\mathrm{ideleNorm}_K$ — the value at the argument of the distributive Haar character of $\mathbb{A}_K$, read as a nonnegative real and then as a real — of the determinant of the scalar $2 \times 2$ invertible matrix $\mathrm{diag}(z,z)$, i.e. of [`AutomorphicForm.centralScalar`](def/AutomorphicForm_AdelicLsXi.html#L18) applied to $z$, lies in the closed interval $[\alpha,\beta]$. The assertion is that the real number obtained from the $\nu$-measure of this subset by `ENNReal.toReal`, viewed as a complex number, is nonzero; equivalently, that measure is neither $0$ nor $\infty$.
--
--   This is the positivity-and-finiteness input for the normalising constant attached to a determinant-norm band in the adelic theory of $\mathrm{GL}_2$ zeta integrals over a number field, in the style of Tate's thesis. It is used in the construction of a continuous automorphic datum with prescribed non-Eisenstein, atomless behaviour and controlled geometric remainder.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_toReal_measure_inter_setOf_ideleNorm_det_centralScalar_mem_Icc_ne_zero.lean

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.toReal_measure_inter_setOf_ideleNorm_det_centralScalar_mem_Icc_ne_zero
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK) :
    ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
          (Matrix.GeneralLinearGroup.det (AutomorphicForm.centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal :
        ℂ) ≠ 0 := by sorry
