-- Prove2me | Theorems.Thm_AutomorphicForm_exists_eisensteinTableOf_eq_formalBaseChange_eisensteinTableOf
-- name    : AutomorphicForm.exists_eisensteinTableOf_eq_formalBaseChange_eisensteinTableOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/082d7873-7101-5811-8ae8-3868dda2ba6f
-- title:
--   Formal base change of an Eisenstein Hecke table is Eisenstein
-- statement:
--   Let $L/K$ be a finite Galois extension of number fields, let $S_K$ and $S_L$ be finite sets of finite places of $K$ and of $L$ with the properties that every $w$ of $L$ whose restriction $v = w\cap\mathcal O_K$ lies in $S_K$ lies in $S_L$, and that every $w$ with $v\notin S_K$ satisfies $\mathrm{ramificationIdx}'(v,w)=1$; let $M\neq 0$ be an ideal of $\mathcal O_K$ and let $\chi_1,\chi_2\colon \mathbb A_K^\times\to\mathbb C^\times$ be monoid homomorphisms that are continuous as $\mathbb C$-valued functions, trivial on the image of $K^\times$, and unramified at every $v\notin S_K$ in the sense that $\chi_i$ kills every local unit $t$ at $v$ with $t$ and $t^{-1}$ integral. Then there exist a nonzero ideal $M'$ of $\mathcal O_L$ and monoid homomorphisms $\chi_1',\chi_2'\colon\mathbb A_L^\times\to\mathbb C^\times$, again continuous and trivial on $L^\times$, such that for every $w\notin S_L$, writing $f=\mathrm{inertiaDeg}'(v,w)$ and $\varpi$ for the idele attached to a local uniformiser, the pair $\bigl(\mathrm{satakePow}\,f\,(\chi_1(\varpi_v)+\chi_2(\varpi_v))\,(\chi_1(\varpi_v)\chi_2(\varpi_v)),\ (\chi_1(\varpi_v)\chi_2(\varpi_v))^f\bigr)$ coming from `formalBaseChange` of the Eisenstein table of $(M,\chi_1,\chi_2)$ equals $\bigl(\chi_1'(\varpi_w)+\chi_2'(\varpi_w),\ \chi_1'(\varpi_w)\chi_2'(\varpi_w)\bigr)$, the Eisenstein table of $(M',\chi_1',\chi_2')$ at $w$.
--
--   This is the base change of principal-series (Eisenstein) Hecke data for $\mathrm{GL}_2$, in the purely formal shape used by the project: the formal base change operation on Hecke eigensystems sends an Eisenstein table over $K$ to an Eisenstein table over $L$, for the norm-composed characters, at all places outside the exceptional set. It is used in the analysis of twisted cut traces for base-changed eigensystems.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_eisensteinTableOf_eq_formalBaseChange_eisensteinTableOf.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_DedekindDomain_IntegralClosure
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain MeasureTheory NumberField.AdelicHaar AutomorphicForm NumberField.TateGlobal AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering LocalGL2
open scoped TensorProduct Pointwise TensorProduct.RightActions ComplexConjugate BigOperators NumberField NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_eisensteinTableOf_eq_formalBaseChange_eisensteinTableOf
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL)
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∉ SK →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (h1c : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₁ z : ℂˣ) : ℂ))
    (h1t : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ₁ z = 1)
    (h2c : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₂ z : ℂˣ) : ℂ))
    (h2t : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ₂ z = 1)
    (hunr : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
      NumberField.TateGlobal.IsUnramifiedCharAt χ₁ v ∧ NumberField.TateGlobal.IsUnramifiedCharAt χ₂ v) :
    ∃ (M' : Ideal (𝓞 L)) (hM' : M' ≠ ⊥) (χ₁' χ₂' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
      (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₁' z : ℂˣ) : ℂ)) ∧
      (∀ z : (AdeleRing (𝓞 L) L)ˣ,
        z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
          χ₁' z = 1) ∧
      (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₂' z : ℂˣ) : ℂ)) ∧
      (∀ z : (AdeleRing (𝓞 L) L)ˣ,
        z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
          χ₂' z = 1) ∧
      ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
        ((formalBaseChange K L (LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂)).a w,
          (formalBaseChange K L (LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂)).b w) =
        ((LanglandsTunnell.Converse.eisensteinTableOf L M' hM' χ₁' χ₂').a w,
          (LanglandsTunnell.Converse.eisensteinTableOf L M' hM' χ₁' χ₂').b w) := by sorry
