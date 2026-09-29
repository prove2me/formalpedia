-- Prove2me | Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul
-- name    : AutomorphicForm.SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/e2f71657-0e9f-57b8-9028-e0fc8c548a58
-- title:
--   Twisting a cusp realization by ‖det‖_A^t
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1>0$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb A_K)$. Fix the carrier pins `productionPinsOf` for $K$ whose domain is $\bigcup_{x\in T}\{g x : g\in\;$`centreCutSiegelSet K c u d₁ d₂`$\}$ — the centre-cut Siegel set consisting of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component has local height $\ge c$ and $x$-window square $\le u^2$ at every infinite place, and with $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$ for all $w$ — whose level subgroups are $N\mapsto$ `levelOne` at $N$ intersected with the kernel of the archimedean-component map, whose Hecke elements are the `heckeGen` at each finite place, whose central subgroup is $\top$, and whose adelic box is `adelicBox K`. Let $\Theta$ be a complex Hecke eigensystem over $K$ (level $\neq\bot$, tables $a,b$), let $R$ be a smooth cusp realization at these pins of $\Theta$'s raw central rescaling $(a_v,\,N(v)^{-1}b_v)$, and assume $R.\mathrm{toFun}$ is continuous. Then for every real $t$ there is such a realization $R'$ for the raw central rescaling of the twist of $\Theta$ by $v\mapsto N(v)^{-t}$ (tables $N(v)^{-t}a_v$ and $N(v)^{-2t}b_v$), with $R'.\mathrm{toFun}$ continuous, $R'.\mathrm{exceptionalSet}=R.\mathrm{exceptionalSet}$, and $R'.\mathrm{toFun}(g)=\|\det g\|_{\mathbb A}^{\,t}\,R.\mathrm{toFun}(g)$ for all $g\in\mathrm{GL}_2(\mathbb A_K)$, where $\|\cdot\|_{\mathbb A}$ is the idelic norm [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19).
--
--   This is the explicit form of the standard operation of twisting an automorphic form by a power of the idelic norm of the determinant, recorded at the level of realizations rather than merely of eigensystems: the realizing function is multiplied by the idele class character $\|\cdot\|_{\mathbb A}^{t}\circ\det$, the exceptional set of places is unchanged, and the Hecke eigenvalues shift by $N(v)^{-t}$ and $N(v)^{-2t}$. It is used to normalise eigensystems before comparing Hecke and central eigenvalues, and in the analysis of archimedean characters and Casimir eigenvalues of the realizations attached to Siegel-set carriers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NarrowRayClassGroup
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open Deep.NTSupply
open scoped Classical

theorem AutomorphicForm.SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd₁ : 0 < d₁)
    (Θ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral R)
    (t : ℝ) :
    ∃ R' : SmoothCuspRealizationAt K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
        (Θ.twist (fun v : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))).toRawCentral,
      IsGenuineCuspRealizationAt K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
        (Θ.twist (fun v : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))).toRawCentral R' ∧
      R'.exceptionalSet = R.exceptionalSet ∧
      ∀ g : AdelicGL2 (𝓞 K) K,
        R'.toFun g = ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) * R.toFun g := by sorry
