-- Prove2me | Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_a_sq_ne_b_mul_of_not_dvd_level_of_not_mem_exceptionalSet
-- name    : AutomorphicForm.SmoothCuspRealizationAt.a_sq_ne_b_mul_of_not_dvd_level_of_not_mem_exceptionalSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/eeb902bf-dccb-5ebe-8389-fff18e11c502
-- title:
--   Genericity at places off the level and exceptional set
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$, and assume $0<c$, $0<d_1$ and $d_1<d_2$. Write $D=\bigcup_{x\in T}\,(\,\cdot\,x)\bigl(\mathcal{S}\bigr)$ for the union of the right translates by the elements of $T$ of the centre-cut Siegel set $\mathcal{S}$, i.e. of the set of $g$ whose finite component is integral, whose archimedean component has local height at least $c$ and window quantity $\mathrm{xWindowSq}\le u^2$ at every infinite place, and whose archimedean determinant norm lies in $[d_1,d_2]$ at every infinite place; assume $D$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo left translation by $\mathrm{GL}_2(K)$ and right multiplication by the adelic central scalars. Let $\Theta$ be a complex Hecke eigensystem over $K$, i.e. a nonzero level ideal $\mathfrak{n}$ of $\mathcal{O}_K$ together with functions $v\mapsto a_v$, $v\mapsto b_v$ on the finite places. Let $R$ be a smooth cusp realization, at the production pins attached to $D$ (adelic Haar measure and Borel structure on $\mathrm{GL}_2(\mathbb{A}_K)$, full central subgroup, level subgroups $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, Hecke generators $\mathrm{heckeGen}_v$, and the additive adelic measure conditioned on the adelic box), of the raw recentring $\Theta.\mathrm{toRawCentral}$ of $\Theta$, whose central eigenvalues are $N(v)^{-1}b_v$ and whose Hecke eigenvalues are $a_v$: thus $R$ consists of a function $R.\mathrm{toFun}$ on $\mathrm{GL}_2(\mathbb{A}_K)$ that is not identically zero, a central character, the smooth-cusp-automorphy condition, invariance under the level subgroup at $\mathfrak{n}$, a finite exceptional set, and the Hecke and central eigenfunction equations at all places outside that set. Assume furthermore that $R.\mathrm{toFun}$ is continuous. Then for every finite place $v$ with $v\nmid\mathfrak{n}$ and $v\notin R.\mathrm{exceptionalSet}$ one has $a_v^2\neq b_v\bigl(N(v)+2+N(v)^{-1}\bigr)$, where $N(v)$ is the absolute norm of $v$.
--
--   With $a_v=\alpha_1+\alpha_2$ and $b_v=\alpha_1\alpha_2$ the conclusion says $\alpha_1/\alpha_2\notin\{N(v),N(v)^{-1}\}$, i.e. the unramified local component at $v$ of the realized eigensystem lies off the reducible locus (genericity at good places); note that both sides are homogeneous of the same degree under $(a,b)\mapsto(\chi a,\chi^2 b)$, so no unitary normalisation of $\Theta$ is required. It is used in the construction of the Rankin–Selberg Euler products, where non-vanishing of the local factor at $N(v)^{-1}$ and the order of the completed product at $s=1$ are needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_a_sq_ne_b_mul_of_not_dvd_level_of_not_mem_exceptionalSet.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NarrowRayClassGroup
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.Analysis.Meromorphic.Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open Deep.NTSupply
open scoped Classical

theorem AutomorphicForm.SmoothCuspRealizationAt.a_sq_ne_b_mul_of_not_dvd_level_of_not_mem_exceptionalSet
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral R) :
    ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ Θ.level → v ∉ R.exceptionalSet →
      Θ.a v ^ 2 ≠ Θ.b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 2 + ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹) := by sorry
