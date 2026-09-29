-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_forall_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self
-- name    : AutomorphicForm.exists_finset_forall_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/67159aa8-40e5-5199-ac5c-760d00ef186b
-- title:
--   Partial Rankin–Selberg L-function: simple pole at s=1
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $0<c$, $0<d_1<d_2$, and let $T$ be a finite set of elements of $\mathrm{GL}_2$ over the adele ring of $K$. Write $D=\bigcup_{x\in T}\{gx : g\in \mathrm{centreCutSiegelSet}\}$, where `centreCutSiegelSet K c u d₁ d₂` consists of those $g$ whose finite component lies in `finiteIntegralGL2` and whose archimedean components satisfy, at every infinite place $w$, $c\le\mathrm{localHeight}$, $\mathrm{xWindowSq}\le u^2$, and $\mathrm{archDetNorm}\,w\,g\in[d_1,d_2]$. It is assumed that $D$ covers modulo the centre: every $g$ admits $\gamma\in\mathrm{GL}_2(K)$ and an adelic unit $z$ with $\gamma g\,\mathrm{diag}(z,z)\in D$. Let $\Theta$ be a Hecke eigensystem over $K$ with values in $\mathbb{C}$, i.e. a nonzero level ideal of $\mathcal O_K$ together with tables $v\mapsto \Theta.a\,v$, $v\mapsto\Theta.b\,v$ on the height-one spectrum, and assume `IsArithGenuineCuspRealizable` for $\Theta$ at the pins `productionPinsOf` built from $D$, the level subgroups $N\mapsto \mathrm{levelOne}(N)\sqcap\ker(\mathrm{glArch})$, the Hecke generators $v\mapsto \mathrm{heckeGen}\,v$ and the box `adelicBox K`; by definition this says that the renormalised eigensystem $\Theta.\mathrm{toRawCentral}$ (same level and $a$, with $b_v$ replaced by $(\mathrm{cNorm}\,v)^{-1}b_v$) admits a smooth cusp realisation at those pins which is genuine. Then there is a finite set $S_1$ of height-one primes of $\mathcal O_K$ such that for every finite set $S\supseteq S_1$ there exist $\sigma_0\in\mathbb{R}$ and $\Lambda:\mathbb{C}\to\mathbb{C}$ with: $\Lambda$ meromorphic on some half-plane $\{\operatorname{Re}s>a\}$ with $a<1$; $\mathrm{meromorphicOrderAt}\,\Lambda\,1=-1$; $\Lambda$ analytic at every real point $\sigma>1$; and, for all $s$ with $\operatorname{Re}s>\sigma_0$, the family indexed by the primes $v\notin S$ of the reciprocals of the values at $X=N(v)^{-s}$ of `rsEulerPoly` with parameters $a=\Theta.a\,v/\Theta.b\,v$, $b=(\Theta.b\,v)^{-1}$, $e_1=\Theta.a\,v$, $e_2=\Theta.b\,v$, $e_3=0$ is multipliable with product $\Lambda(s)$. (For $\Theta.b\,v\neq0$ that polynomial is the quartic $1-\tfrac{a_v^2}{b_v}X+\bigl(\tfrac{2a_v^2}{b_v}-2\bigr)X^2-\tfrac{a_v^2}{b_v}X^3+X^4=(1-X)^2(1-\alpha_1\alpha_2^{-1}X)(1-\alpha_2\alpha_1^{-1}X)$, where $\alpha_1+\alpha_2=a_v$, $\alpha_1\alpha_2=b_v$.)
--
--   This is the form, monotone in the excluded set of places, of the Jacquet–Shalika statement that the partial Rankin–Selberg $L$-function of a cuspidal automorphic representation of $\mathrm{GL}_2$ against its contragredient has a simple pole at $s=1$ and no other singularity on the real axis beyond it; it is obtained from the single-set version [`AutomorphicForm.exists_finset_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self`](thm.html#AutomorphicForm.exists_finset_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self). The version quantified over all sufficiently large $S$ is what is used to derive the logarithmic bound on $\sum_v \lVert a_v\rVert^2 N(v)^{-\sigma}$ for cusp-realizable eigensystems.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_forall_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self.lean

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

theorem AutomorphicForm.exists_finset_forall_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ)
    (hΘ : IsArithGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), ∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ S →
      ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
      (∃ a : ℝ, a < 1 ∧ MeromorphicOn Λ {s : ℂ | a < s.re}) ∧
      meromorphicOrderAt Λ 1 = -1 ∧
      (∀ σ : ℝ, 1 < σ → AnalyticAt ℂ Λ (σ : ℂ)) ∧
      ∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v.1 / Θ.b v.1) (Θ.b v.1)⁻¹
              (Θ.a v.1) (Θ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s) := by sorry
