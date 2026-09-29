-- Prove2me | Theorems.Thm_AutomorphicForm_RankinSelberg_section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd
-- name    : AutomorphicForm.RankinSelberg.section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/8172bb52-2342-5906-b052-b8cbfc1dd984
-- title:
--   Induced sections on the torus: φₛ(diag(t,1)k)=‖t‖^{s+1/2}φₛ(k)
-- statement:
--   Let $K$ be a number field and let $\alpha : \mathbb{A}_K^\times \to \mathbb{R}^\times$ be the character of the idele group obtained from the distributive Haar character `distribHaarChar` of the adele ring $\mathbb{A}_K =$ `AdeleRing (𝓞 K) K` by composing with the coercion $\mathbb{R}_{\ge 0} \to \mathbb{R}$ and passing to units. Assume $\alpha(t) > 0$ for all $t$ (hypothesis $h\alpha$), and let $\varphi : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be a family of functions such that for every $s$ the function $\varphi_s$ is an induced section for the pair of characters `etaFst 1 α hα s` $= \alpha^{s+1/2}$ and `etaSnd 1 α hα s` $= \alpha^{-(s+1/2)}$ (the trivial character times the complex power `cpowChar`); that is, $\varphi_s(bg) = \chi_1(b_{00})\,\chi_2(b_{11})\,\varphi_s(g)$ for every $b$ in the adelic Borel subgroup (matrices with $b_{10} = 0$) and every $g \in \mathrm{GL}_2(\mathbb{A}_K)$. Then for every $s \in \mathbb{C}$, every $k$ lying in `adelicMaximalCompact K` (finite part integral, each archimedean component a row isometry) and every idele $t$, one has $\varphi_s(\mathrm{diag}(t,1)\,k) = \|t\|^{\,s+1/2}\,\varphi_s(k)$, where $\|t\| =$ [`NumberField.TateGlobal.ideleNorm K t`](def/NumberField_TateGlobalZeta.html#L19) is the value of `distribHaarChar` at $t$.
--
--   This is the elementary transformation law of a section of the principal series induced from the characters $(\|\cdot\|^{s+1/2}, \|\cdot\|^{-(s+1/2)})$ of the diagonal torus of $\mathrm{GL}_2(\mathbb{A}_K)$, restricted to the torus elements $\mathrm{diag}(t,1)$ acting on the left. It is used in the Rankin–Selberg estimates, feeding into [`AutomorphicForm.RankinSelberg.exists_finset_norm_whittakerCoefficient_sq_mul_norm_section_le_shell_indicator_of_shell_surgery`](thm.html#AutomorphicForm.RankinSelberg.exists_finset_norm_whittakerCoefficient_sq_mul_norm_section_le_shell_indicator_of_shell_surgery).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_RankinSelberg_section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd.lean

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem AutomorphicForm.RankinSelberg.section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s)),
    ∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K), k ∈ adelicMaximalCompact K → ∀ t : (AdeleRing (𝓞 K) K)ˣ,
        φ s (diagOne t * k) = ((NumberField.TateGlobal.ideleNorm K t : ℝ) : ℂ) ^ (s + 1 / 2) * φ s k := by sorry
