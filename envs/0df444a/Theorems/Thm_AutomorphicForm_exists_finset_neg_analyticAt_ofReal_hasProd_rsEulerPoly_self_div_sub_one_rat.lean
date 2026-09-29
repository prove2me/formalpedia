-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_neg_analyticAt_ofReal_hasProd_rsEulerPoly_self_div_sub_one_rat
-- name    : AutomorphicForm.exists_finset_neg_analyticAt_ofReal_hasProd_rsEulerPoly_self_div_sub_one_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/fdf0b3ef-e80b-5879-8c2f-ff12163b32fe
-- title:
--   Regularised partial Rankin–Selberg product over ℚ
-- statement:
--   Let $c,u,d_1,d_2$ be real numbers with $0<c$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$. Write $D$ for the union over $x\in T$ of the right translates $(\cdot\,x)$ of the centre-cut Siegel set $\mathrm{centreCutSiegelSet}\ \mathbb{Q}\ c\ u\ d_1\ d_2$, consisting of those $g$ whose finite part is integral and whose archimedean component at each infinite place has local height at least $c$, squared $x$-window at most $u^2$, and archimedean determinant norm in $[d_1,d_2]$. Assume $D$ covers $\mathrm{GL}_2(\mathbb{A})$ modulo left translation by $\mathrm{GL}_2(\mathbb{Q})$ and right multiplication by adelic central scalars. Let $\Theta$ be a Hecke eigensystem over $\mathbb{Q}$ with complex values, i.e. a nonzero level ideal together with tables $a,b$ indexed by the primes of $\mathbb{Z}$, and assume `IsArithGenuineCuspRealizable` holds for $\Theta$ at the production pins built from $D$, the levels $\mathrm{levelOne}\ N \sqcap \ker(\mathrm{glArch})$, the Hecke generators $\mathrm{heckeGen}\ v$ and the adelic box; by definition this is genuine cusp realizability of the arithmetically renormalised system $(a_v,(cNorm\,v)^{-1}b_v)$. Then there are a finite set $S$ of primes, reals $\sigma_0$ and $x<0$, and a function $A:\mathbb{C}\to\mathbb{C}$ such that $A$ is analytic at $(\sigma:\mathbb{C})$ for every real $\sigma>x$, and for every $s$ with $\operatorname{Re} s>\sigma_0$ the family indexed by the primes $v\notin S$ of the inverses of $\mathrm{rsEulerPoly}(a_v/b_v,\,b_v^{-1},\,a_v,\,b_v,\,0)$ evaluated at $N(v)^{-s}$ has product $A(s)/(s-1)$. The fifth argument being $0$, the Euler polynomial is $1-(a_v^2/b_v)X+(a_v^2/b_v+a_v^2/b_v-2)X^2\cdots$ in the explicit form given by the definition, of degree at most $4$. No claim is made about $A$ off the real ray beyond this identity on $\operatorname{Re} s>\sigma_0$.
--
--   The function $A$ is the partial Rankin–Selberg $L$-function $L^S(s,\Theta\times\widetilde\Theta)$ multiplied by $s-1$, so the statement records that this regularisation extends analytically across $s=1$ and along a real ray reaching to the left of $0$, while retaining its Euler product on a right half-plane. It feeds the non-vanishing statement [`AutomorphicForm.apply_one_ne_zero_of_differentiable_of_hasProd_eulerProduct_twist_of_norm_eq_one_rat`](thm.html#AutomorphicForm.apply_one_ne_zero_of_differentiable_of_hasProd_eulerProduct_twist_of_norm_eq_one_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_neg_analyticAt_ofReal_hasProd_rsEulerPoly_self_div_sub_one_rat.lean

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

theorem AutomorphicForm.exists_finset_neg_analyticAt_ofReal_hasProd_rsEulerPoly_self_div_sub_one_rat
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Θ : HeckeEigensystem ℚ ℂ)
    (hΘ : IsArithGenuineCuspRealizable ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)) Θ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 ℚ)), ∃ σ₀ x : ℝ, x < 0 ∧ ∃ A : ℂ → ℂ,
      (∀ σ : ℝ, x < σ → AnalyticAt ℂ A (σ : ℂ)) ∧
      (∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v.1 / Θ.b v.1) (Θ.b v.1)⁻¹
              (Θ.a v.1) (Θ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
          (A s / (s - 1))) := by sorry
