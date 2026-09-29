-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuous_forall_principalIdeles_eLpNorm_sub_lt_of_memLp_withDensity_ideleNorm_inv_prod_maximalCompactHaar
-- name    : AutomorphicForm.exists_continuous_forall_principalIdeles_eLpNorm_sub_lt_of_memLp_withDensity_ideleNorm_inv_prod_maximalCompactHaar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/5c347ff0-8a4b-54ce-ad43-8ddff513fae5
-- title:
--   Continuous F^×-invariant functions are L²-dense
-- statement:
--   Let $F$ be a number field. Let $D$ be a measurable subset of the idele group $(\mathbb{A}_F)^\times = (\mathrm{AdeleRing}(\mathcal{O}_F,F))^\times$ which is a fundamental domain, in the sense of `IsFundamentalDomain`, for the action of the subgroup [`M4aHerbrand.principalIdeles`](def/M4aHerbrand_IdeleClassVocab.html#L16) — the image of $F^\times$ under the units map induced by $F \to \mathbb{A}_F$ — with respect to the Haar measure [`NumberField.Idele.idelicHaar`](def/NumberField_IdeleProductMeasure.html#L391) on the idele group (the measurable structures on the adeles, on the ideles and on $GL_2$ of the adeles being the Borel ones). Write $\rho_D$ for the product of, on the first factor, the restriction of `idelicHaar` to $D$ weighted by the density $t \mapsto \mathrm{ofReal}\big((\mathrm{ideleNorm}\,t)^{-1}\big)$, where $\mathrm{ideleNorm}\,t$ is the value at $t$ of the distributive Haar character of $\mathbb{A}_F$, and, on the second factor, the Haar measure `maximalCompactHaar` on the subgroup `adelicMaximalCompact` of $GL_2(\mathbb{A}_F)$ consisting of those $k$ whose finite part lies in `finiteIntegralGL2` and whose component at each infinite place $w$ satisfies `IsRowIsometry` (determinant of absolute value $1$ and preservation of $\|x\|^2+\|y\|^2$ by the row action). Let $f : (\mathbb{A}_F)^\times \times \mathbf{K} \to \mathbb{C}$ satisfy $f(\gamma t, k) = f(t,k)$ for all $\gamma$ in `principalIdeles`, and suppose $f \in L^2(\rho_D)$. Then for every real $\delta > 0$ there exists a continuous $G : (\mathbb{A}_F)^\times \times \mathbf{K} \to \mathbb{C}$, again satisfying $G(\gamma t, k) = G(t,k)$ for all $\gamma$ in `principalIdeles`, with $\mathrm{eLpNorm}(f - G, 2, \rho_D) < \mathrm{ofReal}\,\delta$.
--
--   This is the density, in $L^2$ of the twisted measure $\|t\|^{-1}d^\times t|_D \otimes dk$, of the continuous functions that are invariant under the principal ideles — the invariant form of the standard density of $C_c$ in $L^p$, transported through the quotient by $F^\times$. It feeds the construction of continuous invariant approximants in [`AutomorphicForm.exists_continuous_invariant_bandSupported_eLpNorm_sub_lt_of_isSlabProfile`](thm.html#AutomorphicForm.exists_continuous_invariant_bandSupported_eLpNorm_sub_lt_of_isSlabProfile), within the adelic analytic input to the automorphic side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuous_forall_principalIdeles_eLpNorm_sub_lt_of_memLp_withDensity_ideleNorm_inv_prod_maximalCompactHaar.lean

import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_CarrierPins
import Mathlib.Analysis.Meromorphic.NormalForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

theorem AutomorphicForm.exists_continuous_forall_principalIdeles_eLpNorm_sub_lt_of_memLp_withDensity_ideleNorm_inv_prod_maximalCompactHaar
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdeleRing (𝓞 F) F)ˣ) (hDm : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (f : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) → ℂ)
    (hfinv : ∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), f (γ * p.1, p.2) = f p)
    (hf2 : MemLp f 2
      ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
          (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
        (maximalCompactHaar F)))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ G : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) → ℂ, Continuous G ∧
      (∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), G (γ * p.1, p.2) = G p) ∧
      eLpNorm (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) => f p - G p) 2
        ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F)) < ENNReal.ofReal δ := by sorry
