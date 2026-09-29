-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finite_forall_isUnramifiedCharAt_and_localChar_eq_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel
-- name    : AutomorphicForm.exists_finite_forall_isUnramifiedCharAt_and_localChar_eq_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/bddd5c97-2bc6-5a3a-84c9-3efe629add31
-- title:
--   Finitely many local character possibilities at fixed principal level
-- statement:
--   Let $K$ be a number field, $S_K$ a finite set of finite places of $K$, and $N$ an ideal of $\mathcal O_K$ all of whose prime divisors lie in $S_K$ (hypothesis `hN`). Write $\alpha_m$ for the monoid homomorphism $(\mathbb A_K)^\times \to \mathbb R^\times$ obtained from the `distribHaarChar` of the adele ring by composing with $\mathbb R_{\ge 0}\to\mathbb R$ and passing to units, the adele ring carrying its Borel $\sigma$-algebra. Then there exist a natural number $n$ and a list $\rho_1,\dots,\rho_n$ (indexed by `Fin n`) of families $\rho_r = (\rho_r(v))_v$ of characters $(K_v)^\times \to \mathbb C^\times$, one for each finite place $v$, with the following property, the list being chosen before all the following data. Suppose $\alpha_m$ takes positive real values; let $\mu,\nu : (\mathbb A_K)^\times \to \mathbb C^\times$ be characters, $s \in \mathbb C$, and $\varphi : \mathrm{GL}_2(\mathbb A_K) \to \mathbb C$ a function such that: $\varphi$ is an induced section for the pair $(\mu\,\alpha_m^{s+1/2},\ \nu\,\alpha_m^{-(s+1/2)})$, i.e. $\varphi(bg) = \mu(b_{00})\alpha_m(b_{00})^{s+1/2}\,\nu(b_{11})\alpha_m(b_{11})^{-(s+1/2)}\,\varphi(g)$ for every $g$ and every $b$ in the adelic Borel subgroup (matrices with vanishing lower-left entry), where $b_{00},b_{11}$ are the diagonal entries viewed as units; $\varphi \neq 0$; and $\varphi$ is invariant under right translation by every element of $\mathrm{principalLevel}(N)$ that lies in the kernel of the archimedean projection `glArch`. Then (i) for every finite place $v \notin S_K$, both $\mu$ and $\nu$ are unramified at $v$, meaning that their local restrictions along $(K_v)^\times \hookrightarrow (\mathbb A_K)^\times$ are trivial on every $u$ with $u$ and $u^{-1}$ in $\mathcal O_v$; and (ii) there are indices $r,r' \le n$ such that for all $v \in S_K$ and all such $u$, the local character of $\mu$ at $v$ equals $\rho_r(v)$ at $u$ and that of $\nu$ equals $\rho_{r'}(v)$ at $u$.
--
--   This confines the ramification data of the two characters entering a principal-series section of fixed principal level $N$: their conductors are supported in $S_K$, and their restrictions to the local unit groups at places of $S_K$ range over a finite list depending only on $K$, $S_K$ and $N$, uniformly in $\mu$, $\nu$, $s$ and the section. It is used in the finiteness and summability estimates for families of induced sections at fixed level, such as the bounds on orthonormal flat families and the admissible decompositions of flat restrictions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finite_forall_isUnramifiedCharAt_and_localChar_eq_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel.lean

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

theorem AutomorphicForm.exists_finite_forall_isUnramifiedCharAt_and_localChar_eq_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel
    (K : Type) [Field K] [NumberField K]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ (n : ℕ) (ρs : Fin n → ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ),
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ)
      (φ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) φ)
      (_hφ0 : φ ≠ 0)
      (_hφlev : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * u) = φ g),
    (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
      NumberField.TateGlobal.IsUnramifiedCharAt μ v ∧ NumberField.TateGlobal.IsUnramifiedCharAt ν v) ∧
    ∃ r r' : Fin n, ∀ v ∈ SK, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        NumberField.TateGlobal.localChar μ v u = ρs r v u ∧ NumberField.TateGlobal.localChar ν v u = ρs r' v u := by sorry
