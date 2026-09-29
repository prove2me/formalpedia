-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self
-- name    : AutomorphicForm.exists_finset_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/7de961af-f4ec-576e-9619-c54964aa5fde
-- title:
--   Simple pole at s=1 of a partial Rankin–Selberg Euler product
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $0<c$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Put $D=\bigcup_{x\in T}\Sigma x$, where $\Sigma$ is the centre-cut Siegel set of those $g$ whose finite part is finite-integral, whose archimedean component at every infinite place has local height at least $c$ and $x$-window square at most $u^2$, and whose archimedean determinant norm at every infinite place lies in $[d_1,d_2]$. Assume $D$ covers modulo the centre: every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ satisfies $\gamma g z\in D$ for some $\gamma\in\mathrm{GL}_2(K)$ (via `globalPoints`) and some $z\in\mathbb{A}_K^\times$ (via `centralScalar`). Let $\Theta$ be a complex Hecke eigensystem over $K$, i.e. a nonzero level ideal together with families $a_v,b_v\in\mathbb{C}$ indexed by the finite places, and assume `IsArithGenuineCuspRealizable` for $\Theta$ at the pins `productionPinsOf` assembled from $D$, the level subgroups $N\mapsto$ `levelOne` $N\sqcap$ `finiteAdelicGL2Subgroup`, the Hecke generators `heckeGen` $v$, and the adelic box: that is, the renormalised eigensystem `toRawCentral` $\Theta$ (same $a_v$, with $b_v$ replaced by $(\mathrm{cNorm}\,v)^{-1}b_v$) admits a smooth cusp realization at those pins which is genuine. Then there are a finite set $S$ of primes of $\mathcal{O}_K$, a real $\sigma_0$ and a function $\Lambda:\mathbb{C}\to\mathbb{C}$ such that: $\Lambda$ is meromorphic on $\{\operatorname{Re} s>a\}$ for some real $a<1$; its meromorphic order at $s=1$ equals $-1$; $\Lambda$ is analytic at $\sigma$ for every real $\sigma>1$; for every $s$ with $\operatorname{Re} s>\sigma_0$ the unordered product over the primes $v\notin S$ of $P_v(\mathcal{N}(v)^{-s})^{-1}$ converges, with value $\Lambda(s)$, where $P_v$ is `rsEulerPoly` with parameters $(a_v/b_v,\;b_v^{-1},\;a_v,\;b_v,\;0)$, namely $1+C(-Ae_1)X+C(A^2e_2+Be_1^2-2Be_2)X^2+C(-ABe_1e_2)X^3+C(B^2e_2^2)X^4$ for $A=a_v/b_v$, $B=b_v^{-1}$, $e_1=a_v$, $e_2=b_v$ (the terms carrying $e_3$ vanish); and $P_v(\mathcal{N}(v)^{-1})\neq 0$ for every $v\notin S$, $\mathcal{N}$ denoting the absolute norm of the underlying ideal.
--
--   This is the sharp pole statement for the partial Rankin–Selberg $L$-function of a cuspidally realizable $\mathrm{GL}_2$ eigensystem against its contragredient table $(a_v/b_v,b_v^{-1})$: the pole at $s=1$ has order exactly $-1$, together with nonvanishing of the Euler factors at $\mathcal{N}(v)^{-1}$ outside a finite set. It feeds the variant [`AutomorphicForm.exists_finset_forall_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self`](thm.html#AutomorphicForm.exists_finset_forall_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self), and thereby the Rankin–Selberg input to the analytic estimates for Hecke eigenvalues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self.lean

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

theorem AutomorphicForm.exists_finset_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self
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
      meromorphicOrderAt Λ 1 = -1 ∧
      (∀ σ : ℝ, 1 < σ → AnalyticAt ℂ Λ (σ : ℂ)) ∧
      (∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v.1 / Θ.b v.1) (Θ.b v.1)⁻¹
              (Θ.a v.1) (Θ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s)) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        (LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v / Θ.b v) (Θ.b v)⁻¹ (Θ.a v) (Θ.b v) 0).eval
          ((((Ideal.absNorm v.asIdeal : ℕ) : ℂ))⁻¹) ≠ 0 := by sorry
