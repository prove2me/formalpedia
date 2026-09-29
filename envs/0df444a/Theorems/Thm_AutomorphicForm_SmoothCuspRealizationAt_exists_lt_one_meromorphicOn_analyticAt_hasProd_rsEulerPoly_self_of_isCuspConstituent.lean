-- Prove2me | Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_lt_one_meromorphicOn_analyticAt_hasProd_rsEulerPoly_self_of_isCuspConstituent
-- name    : AutomorphicForm.SmoothCuspRealizationAt.exists_lt_one_meromorphicOn_analyticAt_hasProd_rsEulerPoly_self_of_isCuspConstituent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/9b1f2f0f-e614-5de0-b3e2-d9750339ff53
-- title:
--   Rankin–Selberg Euler product for a cuspidal-constituent cusp realization
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real with $0<c$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$ such that $D=\bigcup_{x\in T}(\,\cdot\,x)\,[\,\mathrm{centreCutSiegelSet}\,K\,c\,u\,d_1\,d_2\,]$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo $\mathrm{GL}_2(K)$ on the left and the adelic centre on the right; here the centre-cut Siegel set consists of those $g$ whose finite part is integral, whose archimedean component at every infinite place has local height $\ge c$, window $x$-coordinate squared $\le u^2$, and determinant norm in $[d_1,d_2]$. Let $\Theta$ be a Hecke eigensystem over $K$ with values in $\mathbb{C}$ (a nonzero level ideal $\mathfrak n$ together with tables $a_v,b_v$), and let $R$ be a smooth cusp realization, at the production pins built from $D$, the levels $U(N)=\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, the Hecke generators $\mathrm{heckeGen}(v)$ and the adelic box, of the raw rescaling $\Theta.\mathrm{toRawCentral}$ of $\Theta$ (same level and $a_v$, with $b_v$ replaced by $b_v/|\!|\mathfrak p_v|\!|$); assume $R$'s function is continuous. Let $tys$ be an archimedean type family (finitely many representations of the row-isometry subgroup at each infinite place) and let $V$ be a $\mathbb{C}$-submodule of functions on $\mathrm{GL}_2(\mathbb{A}_K)$ that is a cuspidal constituent for the central character of $R$: a nonzero cuspidal $K$-finite subrepresentation, stable under right translation by finite adelic elements and by archimedean row isometries and under right convolution by factorizable archimedean-bifinite test functions, and minimal among such subrepresentations. Assume finally that $R$'s function lies in $V$, is invariant under right multiplication by $U(\mathfrak n)$, and lies in the archimedean cut submodule $\bigsqcap_w\bigvee_i$ of the given types. Then there exist a finite set $S$ of height-one primes of $\mathcal O_K$ such that every $v\notin S$ neither divides $\mathfrak n$ nor belongs to $R$'s exceptional set, a real $\sigma_0$, and a function $\Lambda:\mathbb{C}\to\mathbb{C}$ such that $\Lambda$ is meromorphic on some half-plane $\{\operatorname{Re}s>a\}$ with $a<1$, has meromorphic order $<0$ at $s=1$, is analytic at every real point $\sigma>1$, and satisfies, for all $s$ with $\operatorname{Re}s>\sigma_0$, that the family of reciprocals of $\mathrm{rsEulerPoly}(a_v/b_v,\;b_v^{-1},\;a_v,\;b_v,\;0)$ evaluated at $|\!|\mathfrak p_v|\!|^{-s}$, indexed by the primes $v\notin S$, has product $\Lambda(s)$.
--
--   This is the analytic half of the pole statement for the partial Rankin–Selberg $L$-function $L^S(s,\Theta\times\widetilde\Theta)$ at the grain of a single cusp realization lying in one cuspidal constituent: meromorphic continuation slightly past $1$, a pole at $s=1$, analyticity on the real axis beyond $1$, and an Euler product in a right half-plane, with the excluded set containing the level and the exceptional set of the realization. It feeds the combined statement [`AutomorphicForm.exists_finset_lt_one_meromorphicOn_analyticAt_hasProd_rsEulerPoly_self_and_eval_inv_absNorm_ne_zero`](thm.html#AutomorphicForm.exists_finset_lt_one_meromorphicOn_analyticAt_hasProd_rsEulerPoly_self_and_eval_inv_absNorm_ne_zero), where it is paired with nonvanishing of the local factors at the good places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_lt_one_meromorphicOn_analyticAt_hasProd_rsEulerPoly_self_of_isCuspConstituent.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NarrowRayClassGroup
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.Analysis.Meromorphic.Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent
open IsDedekindDomain
open Deep.NTSupply
open scoped Classical

theorem AutomorphicForm.SmoothCuspRealizationAt.exists_lt_one_meromorphicOn_analyticAt_hasProd_rsEulerPoly_self_of_isCuspConstituent
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
        (adelicBox K)) Θ.toRawCentral R)
    (tys : AutomorphicForm.ArchTypeFamily K)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) R.centralChar V)
    (hRV : R.toFun ∈ V ⊓ levelInvariantSubmodule K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.level ⊓ archCutSubmodule K tys) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ¬ v.asIdeal ∣ Θ.level ∧ v ∉ R.exceptionalSet) ∧
      ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
        (∃ a : ℝ, a < 1 ∧ MeromorphicOn Λ {s : ℂ | a < s.re}) ∧
        meromorphicOrderAt Λ 1 < 0 ∧
        (∀ σ : ℝ, 1 < σ → AnalyticAt ℂ Λ (σ : ℂ)) ∧
        ∀ s : ℂ, σ₀ < s.re →
          HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
            ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v.1 / Θ.b v.1) (Θ.b v.1)⁻¹
                (Θ.a v.1) (Θ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s) := by sorry
