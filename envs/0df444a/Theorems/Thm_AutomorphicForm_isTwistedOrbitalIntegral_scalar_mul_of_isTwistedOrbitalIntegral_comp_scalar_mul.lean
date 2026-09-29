-- Prove2me | Theorems.Thm_AutomorphicForm_isTwistedOrbitalIntegral_scalar_mul_of_isTwistedOrbitalIntegral_comp_scalar_mul
-- name    : AutomorphicForm.isTwistedOrbitalIntegral_scalar_mul_of_isTwistedOrbitalIntegral_comp_scalar_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/034ee9aa-6135-56e5-9aaa-9cfff9898eae
-- title:
--   Central translation for local twisted orbital integrals
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ finite, let $\sigma$ be a $K$-algebra automorphism of $L$, let $v$ be a nonzero prime of $\mathcal{O}_K$, and write $R_v = L \otimes_K K_v$ for the semilocal algebra at $v$. Fix $\delta \in \mathrm{GL}_2(R_v)$ and a unit $c \in R_v^{\times}$, and let $\mathrm{scalar}(c) \in \mathrm{GL}_2(R_v)$ be the corresponding scalar matrix. For $\gamma \in \mathrm{GL}_2(R_v)$, the twisted centraliser of $\gamma$ is the subgroup $\{t : t\gamma\,\sigma(t)^{-1} = \gamma\}$, where $\sigma$ acts entrywise through `sigmaGL`. Let $\tau'$ be a Haar measure (for the Borel structure) on the twisted centraliser of $\delta$, and $\tau''$ one on the twisted centraliser of $\mathrm{scalar}(c)\,\delta$, each assigning mass $1$ to the intersection of its group with the set of $g \in \mathrm{GL}_2(R_v)$ such that both $g$ and $g^{-1}$ have all entries in the image of $\mathcal{O}_L \otimes \mathcal{O}_{K_v}$ in $R_v$. Let $\varphi_v : \mathrm{GL}_2(R_v) \to \mathbb{C}$ and $I \in \mathbb{C}$. Assume $I$ is a twisted orbital integral at $\delta$ with respect to $\tau'$ of the translated function $x \mapsto \varphi_v(\mathrm{scalar}(c)\,x)$, i.e. there is $w : \mathrm{GL}_2(R_v) \to \mathbb{R}$ satisfying `IsTwistedSectionFnOn` for these data and $I = \int \varphi_v(\mathrm{scalar}(c)\,x^{-1}\delta\,\sigma(x))\, w(x)$ against the Haar measure `semiLocalHaar` on $\mathrm{GL}_2(R_v)$. Then the same number $I$ is a twisted orbital integral of $\varphi_v$ itself at $\mathrm{scalar}(c)\,\delta$ with respect to $\tau''$.
--
--   This is the central-translation compatibility of local twisted orbital integrals: translating the test function by a central element is the same as translating the twisted class by that element, the two twisted centralisers and their unit-normalised Haar measures matching up. It is used when a central translate produced by unfolding the centre is moved onto the class, so that scale-invariant local bounds on normalised weights apply; it is cited by [`AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure`](thm.html#AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure) and by [`AutomorphicForm.norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_comp_scalar_mul`](thm.html#AutomorphicForm.norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_comp_scalar_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isTwistedOrbitalIntegral_scalar_mul_of_isTwistedOrbitalIntegral_comp_scalar_mul.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.isTwistedOrbitalIntegral_scalar_mul_of_isTwistedOrbitalIntegral_comp_scalar_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (c : (L ⊗[K] v.adicCompletion K)ˣ)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (hτ'1 : τ' (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (τ'' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ))
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ)))
    (hτ'' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ)) τ'')
    (hτ''1 : τ'' (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (I : ℂ)
    (hI : AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ'
      (fun x => φv (Matrix.GeneralLinearGroup.scalar (Fin 2) c * x)) I) :
    AutomorphicForm.IsTwistedOrbitalIntegral K L v σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ) τ'' φv I := by sorry
