-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_lt_one_meromorphicOn_analyticAt_hasProd_rsEulerPoly_self_and_eval_inv_absNorm_ne_zero
-- name    : AutomorphicForm.exists_finset_lt_one_meromorphicOn_analyticAt_hasProd_rsEulerPoly_self_and_eval_inv_absNorm_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/a5dc892e-5128-5a98-97f3-140df8ecb251
-- title:
--   Partial Rankin–Selberg product with a pole at s=1
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $0<c$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2$ of the adeles of $K$. Write $D=\bigcup_{x\in T}\{g x : g\in \mathrm{centreCutSiegelSet}\}$, where `centreCutSiegelSet K c u d₁ d₂` consists of those adelic matrices whose finite part is integral and whose archimedean component at every infinite place has local height at least $c$, window square at most $u^2$, and archimedean determinant norm in $[d_1,d_2]$. Assume `CoversModCentre K D`: for every adelic $g$ there are $\gamma\in\mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g z\in D$ (central scalar $z$). Let $\Theta$ be a Hecke eigensystem over $K$ with values in $\mathbb{C}$, i.e. a nonzero level ideal together with tables $v\mapsto \Theta.a\,v=a_v$ and $v\mapsto \Theta.b\,v=b_v$ indexed by the height-one primes of $\mathcal{O}_K$. Assume `IsArithGenuineCuspRealizable` for $\Theta$ at the pins `productionPinsOf` formed from $D$, the level subgroups $N\mapsto \mathrm{levelOne}(N)\sqcap$ `finiteAdelicGL2Subgroup`, the Hecke generators `heckeGen`, and the adelic box, i.e. the arithmetically renormalised system (with $b_v$ replaced by $(\mathrm{cNorm}\,v)^{-1}b_v$) admits a smooth cusp realisation at those pins which is genuine. Then there exist a finite set $S$ of primes of $\mathcal{O}_K$, a real number $\sigma_0$ and a function $\Lambda:\mathbb{C}\to\mathbb{C}$ such that: $\Lambda$ is meromorphic on $\{\operatorname{Re} s>a\}$ for some real $a<1$; its meromorphic order at $s=1$ is negative; $\Lambda$ is analytic at every real point $\sigma>1$; for every $s$ with $\operatorname{Re} s>\sigma_0$ the family of reciprocals of `rsEulerPoly` $(a_v/b_v,\,b_v^{-1},\,a_v,\,b_v,\,0)$ evaluated at $N(v)^{-s}$, indexed by the primes $v\notin S$, is multipliable with product $\Lambda(s)$; and for every $v\notin S$ the same polynomial evaluated at $N(v)^{-1}$ is nonzero. Here $N(v)=\mathrm{absNorm}$ of the prime ideal, and by the definition of `rsEulerPoly` the polynomial in question is $(1-X)^2\bigl(1-(a_v^2/b_v-2)X+X^2\bigr)$ when $b_v\neq0$ (and is $1$ when $b_v=0$, with Lean's convention $0^{-1}=0$).
--
--   This is the single-excluded-set form of the analytic input on the partial Rankin–Selberg $L$-function $L^S(s,\Theta\times\widetilde\Theta)$ attached to a cusp-realisable $\mathrm{GL}_2$ Hecke eigensystem: meromorphy slightly to the left of $\operatorname{Re} s=1$, a pole at $s=1$, analyticity on the real axis beyond $1$, an Euler product in a right half-plane, and regularity at $s=1$ of every local factor outside $S$. It feeds the monotone pole statement [`AutomorphicForm.exists_lt_one_meromorphicOn_hasProd_rsEulerPoly_self_and_meromorphicOrderAt_one_neg`](thm.html#AutomorphicForm.exists_lt_one_meromorphicOn_hasProd_rsEulerPoly_self_and_meromorphicOrderAt_one_neg) and the Ramanujan-type summability bound [`AutomorphicForm.summable_norm_a_sq_mul_rpow_absNorm_of_isArithGenuineCuspRealizable`](thm.html#AutomorphicForm.summable_norm_a_sq_mul_rpow_absNorm_of_isArithGenuineCuspRealizable).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_lt_one_meromorphicOn_analyticAt_hasProd_rsEulerPoly_self_and_eval_inv_absNorm_ne_zero.lean

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

theorem AutomorphicForm.exists_finset_lt_one_meromorphicOn_analyticAt_hasProd_rsEulerPoly_self_and_eval_inv_absNorm_ne_zero
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ)
    (hΘ : IsArithGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
      (∃ a : ℝ, a < 1 ∧ MeromorphicOn Λ {s : ℂ | a < s.re}) ∧
      meromorphicOrderAt Λ 1 < 0 ∧
      (∀ σ : ℝ, 1 < σ → AnalyticAt ℂ Λ (σ : ℂ)) ∧
      (∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v.1 / Θ.b v.1) (Θ.b v.1)⁻¹
              (Θ.a v.1) (Θ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s)) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        (LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v / Θ.b v) (Θ.b v)⁻¹ (Θ.a v) (Θ.b v) 0).eval
          ((((Ideal.absNorm v.asIdeal : ℕ) : ℂ))⁻¹) ≠ 0 := by sorry
