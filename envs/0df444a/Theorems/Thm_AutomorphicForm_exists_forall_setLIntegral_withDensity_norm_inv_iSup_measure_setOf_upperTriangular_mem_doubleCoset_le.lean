-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setLIntegral_withDensity_norm_inv_iSup_measure_setOf_upperTriangular_mem_doubleCoset_le
-- name    : AutomorphicForm.exists_forall_setLIntegral_withDensity_norm_inv_iSup_measure_setOf_upperTriangular_mem_doubleCoset_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/73fdd8d2-500a-59d5-88be-faa11c572c53
-- title:
--   Uniform shell bound for upper-triangular slices of Hecke double cosets
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $v$ be a nonzero prime of $\mathcal O_K$, write $E = L\otimes_K K_v$ for the semi-local algebra at $v$, equip $E$ with a measurable structure that is the Borel structure of its topology, and let $\nu$ be an additive Haar measure on $E$. Write $\mathcal K =$ [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136) for the set of $g \in \mathrm{GL}_2(E)$ such that the matrices of $g$ and of $g^{-1}$ both lie in `integralMatrixSet` of the semi-local integers `semiLocalIntegers K L v` (the image of $\mathcal O_L$ under the canonical map into $E$), and let $\mu' =$ [`AutomorphicForm.semiLocalHaar K L v`](def/AutomorphicForm_TwistedOrbital.html#L169) be the Haar measure on $\mathrm{GL}_2(E)$, for the Borel structure `glBorelOf`, normalised by $\mu'(\mathcal K) = 1$. Then there exist a finite $C \in [0,\infty]$ and $A \in \mathbb N$ such that for every $a \in \mathrm{GL}_2(E)$ and every real $r$,
--   $$\int_{\{\alpha\,:\,\|N_{E/K_v}\alpha\| = r\}} \Bigl(\sup_{\beta \in E} \nu\bigl\{\xi \in E : \bigl(\begin{smallmatrix}\alpha & \xi\\ 0 & \beta\end{smallmatrix}\bigr) \in \mathcal K\{a\}\mathcal K\bigr\}\Bigr)\, d\bigl(\nu\!\cdot\!\|N_{E/K_v}(\cdot)\|^{-1}\bigr)(\alpha) \le C\,\bigl(\|N_{E/K_v}(\det a)\|\,\mu'(\mathcal K\{a\}\mathcal K)\bigr)^{1/2}\bigl(1 + \log \mu'(\mathcal K\{a\}\mathcal K)\bigr)^{A},$$
--   the integral being the lower Lebesgue integral against $\nu$ with density $\alpha \mapsto \|N_{E/K_v}\alpha\|^{-1}$, and membership in the double coset being taken through the matrix of some $g$ in it. The constants $C$ and $A$ are independent of $a$ and of $r$.
--
--   This is the uniform bound on semi-local Hecke double cosets, measuring the volume of the upper-triangular slices of $\mathcal K a \mathcal K$ over a norm shell in terms of $\|N\det a\|\,\mu'(\mathcal K a\mathcal K)$ with a logarithmic loss accounting for the number of Cartan patterns at the places of $L$ above $v$. It feeds the estimate for twisted orbital integrals of the indicator of a Hecke double coset used in the Rankin–Selberg part of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setLIntegral_withDensity_norm_inv_iSup_measure_setOf_upperTriangular_mem_doubleCoset_le.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.exists_forall_setLIntegral_withDensity_norm_inv_iSup_measure_setOf_upperTriangular_mem_doubleCoset_le
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ A : ℕ,
      ∀ (a : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (r : ℝ),
        ∫⁻ α in {α : L ⊗[K] v.adicCompletion K | ‖Algebra.norm (v.adicCompletion K) α‖ = r},
          (⨆ β : L ⊗[K] v.adicCompletion K,
            ν {ξ : L ⊗[K] v.adicCompletion K |
                ∃ g ∈ AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v,
                  (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = !![α, ξ; 0, β]})
            ∂(ν.withDensity fun b => ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) b‖⁻¹) ≤
        C * ENNReal.ofReal
          ((‖Algebra.norm (v.adicCompletion K)
                ((Matrix.GeneralLinearGroup.det a : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K)‖ *
              (AutomorphicForm.semiLocalHaar K L v
                (AutomorphicForm.semiLocalIntegralSet K L v * {a} *
                  AutomorphicForm.semiLocalIntegralSet K L v)).toReal) ^ ((1 : ℝ) / 2) *
            (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
                (AutomorphicForm.semiLocalIntegralSet K L v * {a} *
                  AutomorphicForm.semiLocalIntegralSet K L v)).toReal) ^ A) := by sorry
