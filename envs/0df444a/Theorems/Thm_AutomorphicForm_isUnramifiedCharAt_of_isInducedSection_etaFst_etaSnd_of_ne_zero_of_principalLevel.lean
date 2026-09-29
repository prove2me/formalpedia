-- Prove2me | Theorems.Thm_AutomorphicForm_isUnramifiedCharAt_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel
-- name    : AutomorphicForm.isUnramifiedCharAt_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/0ba85897-af3e-5111-8d7c-be5ffc668f5c
-- title:
--   Induced sections of level N force characters unramified outside N
-- statement:
--   Let $K$ be a number field and $N$ an ideal of $\mathcal{O}_K$. Write $\alpha$ for the monoid homomorphism $(\mathbb{A}_K)^\times \to \mathbb{R}^\times$ obtained from the module character `distribHaarChar` of the adele ring by composing with the coercion $\mathbb{R}_{\ge 0}\to\mathbb{R}$ and passing to units, and equip $\mathbb{A}_K$ with its Borel $\sigma$-algebra. Assume $\alpha(x)>0$ for all $x$. Let $\mu,\nu : (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ be characters, $s\in\mathbb{C}$, and $\varphi : \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$. Suppose: (i) $\varphi$ is an induced section for the pair $\big(\mu\cdot\alpha^{s+1/2},\ \nu\cdot\alpha^{-(s+1/2)}\big)$, where $\alpha^{w}$ denotes $x\mapsto (\alpha(x))^{w}$ as a complex power of a positive real, that is, $\varphi(bg)=\mu(b_{00})\alpha(b_{00})^{s+1/2}\,\nu(b_{11})\alpha(b_{11})^{-(s+1/2)}\,\varphi(g)$ for every $g$ and every $b\in\mathrm{GL}_2(\mathbb{A}_K)$ with vanishing lower-left entry; (ii) $\varphi\neq 0$; (iii) $\varphi(gu)=\varphi(g)$ for all $g$ and all $u$ in the intersection of `principalLevel (𝓞 K) K N` (the subgroup $\mathrm{levelOne}$ at $N$ intersected with its conjugate by the Weyl element) with the kernel of the archimedean projection $\mathrm{GL}_2(\mathbb{A}_K)\to\mathrm{GL}_2(K\otimes\mathbb{R})$. Then for every $v$ in the height-one spectrum of $\mathcal{O}_K$ with $v\nmid N$, both $\mu$ and $\nu$ satisfy `IsUnramifiedCharAt` at $v$: the local component $\mathrm{localChar}$ of each takes the value $1$ on every unit $t$ of $K_v$ with $t$ and $t^{-1}$ both in the valuation ring.
--
--   This is the adelic form of the standard fact that a non-zero vector in a principal series representation of $\mathrm{GL}_2$ fixed by a maximal compact subgroup at $v$ forces the inducing characters to be unramified at $v$. It feeds the finiteness statement on ramification of the inducing data and, through it, the identification of the atoms of the continuous-spectrum contribution in the $\mathrm{GL}_2$ trace computation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isUnramifiedCharAt_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel.lean

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

theorem AutomorphicForm.isUnramifiedCharAt_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ)
      (φ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) φ)
      (_hφ0 : φ ≠ 0)
      (_hφlev : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * u) = φ g)
      (v : HeightOneSpectrum (𝓞 K)) (_hv : ¬ v.asIdeal ∣ N),
    NumberField.TateGlobal.IsUnramifiedCharAt μ v ∧ NumberField.TateGlobal.IsUnramifiedCharAt ν v := by sorry
