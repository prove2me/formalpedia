-- Prove2me | Theorems.Thm_AutomorphicForm_exists_eisensteinTableOf_eq_table_of_isUnitaryChar_of_isUnramifiedCharAt
-- name    : AutomorphicForm.exists_eisensteinTableOf_eq_table_of_isUnitaryChar_of_isUnramifiedCharAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/98c16b07-f153-5bb2-9d1a-d886a1899167
-- title:
--   Twisted principal-series Hecke table is an Eisenstein table
-- statement:
--   Let $K$ be a number field, $S$ a finite set of finite places of $K$ (a finite set of height-one primes of $\mathcal O_K$) and $w$ a real number. Write $\alpha$ for the homomorphism from the idele group $(\mathbb A_K)^\times$ to $\mathbb R^\times$ obtained from the distributive Haar character of $\mathbb A_K$ (with its Borel structure) followed by $\mathbb R_{\ge 0}\to\mathbb R$, and assume $\alpha$ takes positive values. Let $\mu,\nu:(\mathbb A_K)^\times\to\mathbb C^\times$ be homomorphisms that are unitary ($|\mu(x)|=|\nu(x)|=1$ for all $x$), trivial on the image of $K^\times$, continuous as $\mathbb C$-valued functions, and unramified outside $S$ in the sense that for $v\notin S$ the local component at $v$ is trivial on every unit $t$ of $K_v$ with $t,t^{-1}$ integral. Then there are a non-zero ideal $M\subseteq\mathcal O_K$ and homomorphisms $\chi_1,\chi_2:(\mathbb A_K)^\times\to\mathbb C^\times$, each continuous, trivial on the image of $K^\times$ and unramified outside $S$ in the same sense, such that for every $v\notin S$, with $q_v=\mathrm{N}v$, $|\cdot|^{s}=\alpha(\cdot)^{s}$, $h_v$ the Hecke generator at $v$ and $\varpi_v$ the uniformizer idele,
--   $$\bigl(q_v^{1/2}\bigl(\mu|\cdot|^{w/2}(\det h_v)+\nu|\cdot|^{w/2}(\det h_v)\bigr),\; q_v\,\mu|\cdot|^{w/2}(\det h_v)\,\nu|\cdot|^{w/2}(\det h_v)\bigr)=\bigl(\chi_1(\varpi_v)+\chi_2(\varpi_v),\,\chi_1(\varpi_v)\chi_2(\varpi_v)\bigr),$$
--   the right-hand pair being the $v$-th entries $(a_v,b_v)$ of the Hecke eigensystem [`LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂`](def/LanglandsTunnell_ConverseData.html#L132) of level $M$.
--
--   This identifies the Hecke data of a unitary principal-series pair twisted by the $w/2$ power of the idelic modulus, read along the Hecke generators $\mathrm{diag}(\varpi_v,1)$, with an Eisenstein eigensystem in the sense of the converse-theorem data; the normalising factors $q_v^{1/2}$ and $q_v$ absorb the half-integral shift $|\cdot|^{-1/2}$. It supplies the atom clause for the continuous spectrum in the two statements on the spectral side of the trace formula that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_eisensteinTableOf_eq_table_of_isUnitaryChar_of_isUnramifiedCharAt.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_eisensteinTableOf_eq_table_of_isUnitaryChar_of_isUnramifiedCharAt
    (K : Type) [Field K] [NumberField K]
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (w : ℝ) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hur : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
        NumberField.TateGlobal.IsUnramifiedCharAt μ v ∧ NumberField.TateGlobal.IsUnramifiedCharAt ν v),
    ∃ (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            χ₁ z = 1) ∧
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            χ₂ z = 1) ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
          NumberField.TateGlobal.IsUnramifiedCharAt χ₁ v ∧ NumberField.TateGlobal.IsUnramifiedCharAt χ₂ v) ∧
        ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
          ((HeckeEigensystem.cNorm v) ^ ((1 / 2 : ℝ) : ℂ) *
              ((((μ * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) +
               (((ν * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ)),
            (HeckeEigensystem.cNorm v) *
              (((μ * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) *
              (((ν * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ)) =
          ((LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂).a v,
            (LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂).b v) := by sorry
