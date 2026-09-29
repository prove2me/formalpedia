-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_archCasimirAt_eq_smul_of_mem_isotypicCuspSubmodule_of_mem_archCutSubmodule_of_coversModCentre
-- name    : AutomorphicForm.exists_forall_archCasimirAt_eq_smul_of_mem_isotypicCuspSubmodule_of_mem_archCutSubmodule_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/c56918dc-3eb0-5850-8ce8-373f2ded576c
-- title:
--   A single Casimir eigenvalue on every isotypic cut
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$, $0<d_1<d_2$, let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb A_F)$, and write $D=\bigcup_{x\in T}\{g x: g\in\mathfrak S\}$ for the union of right translates by elements of $T$ of the centre-cut Siegel set $\mathfrak S=$ `centreCutSiegelSet F c u d₁ d₂` (finite part integral, local height $\ge c$ at every infinite place, window quantity `xWindowSq` $\le u^2$, and archimedean determinant norm in $[d_1,d_2]$ at every infinite place). Assume $D$ covers modulo the centre: every $g\in\mathrm{GL}_2(\mathbb A_F)$ admits $\gamma\in\mathrm{GL}_2(F)$ and $z\in\mathbb A_F^\times$ with $\gamma g z\in D$. Let $\Theta$ be a Hecke eigensystem over $\mathbb C$ (a nonzero level ideal together with families $a_v,b_v$ over the finite places) and let $w$ be a real infinite place of $F$, with `archCasimirAt hw` the operator $-\bigl(\tfrac14 H^2-\tfrac12 H+EF\bigr)$ built from the right derivatives along the three one-parameter flows at $w$. Then there is $\lambda\in\mathbb C$ with the following two properties. First, rigidity: for all $n\in\mathbb Z$ and $\lambda'\in\mathbb C$, if there exist an eigensystem $\Theta'$ agreeing with $\Theta$ outside a finite set of finite places and a smooth cusp realization $R'$ for $\Theta'.\mathrm{toRawCentral}$ (the rescaling $b_v\mapsto \mathrm N(v)^{-1}b_v$) at the pins `productionPinsOf F D` (Borel–Haar measure on $\mathrm{GL}_2(\mathbb A_F)$, carrier $D$, full central subgroup, level subgroups `levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F`, Hecke generators `heckeGen`, and additive Haar measure conditioned on the adelic box) whose underlying function is continuous and satisfies the archimedean character condition `HasArchCharacterAt₀` at $w$ for `archWeightCharℝ n` transported along the identification of $w$'s completion with $\mathbb R$, is smooth at $w$ and is a `archCasimirAt hw`-eigenfunction with eigenvalue $\lambda'$, then $\lambda'=\lambda$. Second, every vector: for every such $\Theta'$, every realization $R'$ at those pins for $\Theta'.\mathrm{toRawCentral}$ with continuous underlying function, every finite set $S'$ of finite places, every archimedean type family `tys'`, and every nonzero $x:\mathrm{GL}_2(\mathbb A_F)\to\mathbb C$ lying both in the isotypic cusp submodule at those pins for the central character of $R'$, the level of $\Theta'$, the set $S'$ and $\Theta'$, and in the type-cut submodule `archCutSubmodule F tys'`, the function $x$ is smooth at $w$, all its first and second archimedean derivatives `archDerivAt hw` are continuous, and `archCasimirAt hw x = lam • x`.
--
--   This is the vector-level form of strong multiplicity one at infinity for the Casimir eigenvalue: a single scalar $\lambda$ governs the Casimir action not merely on one occurring eigenvector of the cuspidal class of $\Theta$, but on every vector of every isotypic cut attached to any eigensystem agreeing with $\Theta$ away from finitely many places. It is used on the Langlands–Tunnell side of the argument, where Casimir eigenvalues of weight-one type must be matched across twists and Whittaker expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_archCasimirAt_eq_smul_of_mem_isotypicCuspSubmodule_of_mem_archCutSubmodule_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain

theorem AutomorphicForm.exists_forall_archCasimirAt_eq_smul_of_mem_isotypicCuspSubmodule_of_mem_archCutSubmodule_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ) (w : InfinitePlace F) (hw : w.IsReal) :
    ∃ lam : ℂ,
      (∀ (n : ℤ) (lam' : ℂ),
        ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
            (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
              IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = lam' • φ) →
          lam' = lam) ∧
      (∀ (Θ' : HeckeEigensystem F ℂ), Θ'.AgreesAwayFromFinite Θ →
        ∀ (R' : SmoothCuspRealizationAt F
            (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
            Θ'.toRawCentral), Continuous R'.toFun →
          ∀ (S' : Finset (HeightOneSpectrum (𝓞 F))) (tys' : ArchTypeFamily F) (x : AdelicGL2 (𝓞 F) F → ℂ),
            x ≠ 0 →
            x ∈ isotypicCuspSubmodule F
              (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
              R'.centralChar Θ'.level S' Θ' →
            x ∈ archCutSubmodule F tys' →
              IsArchSmoothAt hw x ∧ (∀ d : ArchDir, Continuous (archDerivAt hw d x)) ∧
                (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) ∧
                archCasimirAt hw x = lam • x) := by sorry
