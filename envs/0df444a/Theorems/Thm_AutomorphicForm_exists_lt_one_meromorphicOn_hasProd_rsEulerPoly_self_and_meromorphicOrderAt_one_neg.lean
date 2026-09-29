-- Prove2me | Theorems.Thm_AutomorphicForm_exists_lt_one_meromorphicOn_hasProd_rsEulerPoly_self_and_meromorphicOrderAt_one_neg
-- name    : AutomorphicForm.exists_lt_one_meromorphicOn_hasProd_rsEulerPoly_self_and_meromorphicOrderAt_one_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/62a8237a-e1f1-5f0a-b0ce-8095f17674e6
-- title:
--   Pole at s=1 of partial Rankin–Selberg Euler products
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Write $D=\bigcup_{x\in T}\{g x : g\in \mathrm{centreCutSiegelSet}\}$ for the union of the right translates by elements of $T$ of the centre-cut Siegel set with parameters $c,u,d_1,d_2$ (those $g$ whose finite part is integral, whose archimedean local heights at every infinite place are at least $c$, whose window coordinates satisfy $\mathrm{xWindowSq}\le u^2$, and whose archimedean determinant norms lie in $[d_1,d_2]$), and assume $D$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo $\mathrm{GL}_2(K)$ on the left and the adelic centre on the right. Let $\Theta$ be a Hecke eigensystem over $K$ with complex values, i.e. a nonzero level ideal of $\mathcal{O}_K$ together with families $v\mapsto \Theta.a\,v$ and $v\mapsto\Theta.b\,v$ indexed by the height-one primes of $\mathcal{O}_K$, and assume that the central renormalisation $\Theta.\mathrm{toRawCentral}$ (same level and same $a$, with $b$ rescaled by $(\mathrm{cNorm}\,v)^{-1}$) admits a genuine smooth cuspidal realisation at the production pins built from the carrier $D$, the adelic Haar data, full central subgroup, the level subgroups $N\mapsto \mathrm{levelOne}\sqcap\mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators $v\mapsto \mathrm{heckeGen}\,v$, and the adelic box $\mathrm{adelicBox}\,K$. Then there is a finite set $S_1$ of height-one primes of $\mathcal{O}_K$ such that for every finite set $S\supseteq S_1$ there exist $\sigma_0\in\mathbb{R}$ and a function $\Lambda:\mathbb{C}\to\mathbb{C}$ with: $\Lambda$ meromorphic on $\{s:\operatorname{Re} s>a\}$ for some real $a<1$; the meromorphic order of $\Lambda$ at $s=1$ negative; and, for every $s$ with $\operatorname{Re} s>\sigma_0$, the family indexed by the primes $v\notin S$ of the reciprocals of $P_v(N(v)^{-s})$ multipliable with product $\Lambda(s)$, where $P_v$ is $\mathrm{rsEulerPoly}$ evaluated at the arguments $a=\Theta.a\,v/\Theta.b\,v$, $b=(\Theta.b\,v)^{-1}$, $e_1=\Theta.a\,v$, $e_2=\Theta.b\,v$, $e_3=0$, so that $$P_v(X)=1-\frac{(\Theta.a\,v)^2}{\Theta.b\,v}X+\Bigl(2\frac{(\Theta.a\,v)^2}{\Theta.b\,v}-2\Bigr)X^2-\frac{(\Theta.a\,v)^2}{\Theta.b\,v}X^3+X^4 .$$
--
--   This is the statement that the partial Rankin–Selberg $L$-function of the eigensystem against its contragredient, whose Euler factors are built from the ratios of the Satake parameters at each prime, has a pole at $s=1$ and continues meromorphically slightly to the left of $\operatorname{Re} s=1$; the form asserted here is monotone in the excluded set $S$, so that excluded sets can be enlarged and synchronised without altering the Euler factors. It is deduced from the version with a single finite exceptional set, [`AutomorphicForm.exists_finset_lt_one_meromorphicOn_analyticAt_hasProd_rsEulerPoly_self_and_eval_inv_absNorm_ne_zero`](thm.html#AutomorphicForm.exists_finset_lt_one_meromorphicOn_analyticAt_hasProd_rsEulerPoly_self_and_eval_inv_absNorm_ne_zero), and feeds the identification of the fibres of cyclic base change in [`AutomorphicForm.HeckeEigensystem.exists_pow_twist_of_isBaseChangeOf_of_isArithGenuineCuspRealizable`](thm.html#AutomorphicForm.HeckeEigensystem.exists_pow_twist_of_isBaseChangeOf_of_isArithGenuineCuspRealizable).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_lt_one_meromorphicOn_hasProd_rsEulerPoly_self_and_meromorphicOrderAt_one_neg.lean

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

theorem AutomorphicForm.exists_lt_one_meromorphicOn_hasProd_rsEulerPoly_self_and_meromorphicOrderAt_one_neg
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
      meromorphicOrderAt Λ 1 < 0 ∧
      ∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v.1 / Θ.b v.1) (Θ.b v.1)⁻¹
              (Θ.a v.1) (Θ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s) := by sorry
