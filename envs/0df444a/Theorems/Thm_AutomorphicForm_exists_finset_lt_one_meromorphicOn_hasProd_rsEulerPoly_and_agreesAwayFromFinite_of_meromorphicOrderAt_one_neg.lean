-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_lt_one_meromorphicOn_hasProd_rsEulerPoly_and_agreesAwayFromFinite_of_meromorphicOrderAt_one_neg
-- name    : AutomorphicForm.exists_finset_lt_one_meromorphicOn_hasProd_rsEulerPoly_and_agreesAwayFromFinite_of_meromorphicOrderAt_one_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/464eb6cf-dbc2-5c67-a14c-42e010b8aec7
-- title:
--   Partial Rankin–Selberg product for two cusp-realizable eigensystems
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $0<c$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Put $D=\bigcup_{x\in T}\{gx: g\in \text{centreCutSiegelSet}\}$, where the centre-cut Siegel set consists of those $g$ whose finite part is integral, whose archimedean component at every infinite place has local height $\ge c$ and $x$-window square $\le u^2$, and whose archimedean determinant norm at every infinite place lies in $[d_1,d_2]$; assume $D$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo $\mathrm{GL}_2(K)$ on the left and the adelic centre on the right. Let $\sigma,\tau$ be Hecke eigensystems over $K$ with complex tables $(a_v,b_v)$ and a nonzero level ideal, both satisfying `IsArithGenuineCuspRealizable` for the production pins built from $D$, the level subgroups $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, the Hecke generators $\mathrm{heckeGen}_v$ and the adelic box (so the pins carry the adelic Borel structures, Haar measure, full central subgroup, and the box-conditioned additive measure), this predicate being realizability of the centrally renormalised table $b_v\mapsto (\mathrm{cNorm}\,v)^{-1}b_v$. Assume $\lVert \sigma.b\,v\rVert=\lVert\tau.b\,v\rVert$ for all $v$ outside some finite set. Then there exist a finite set $S$ of primes of $\mathcal{O}_K$, a real $\sigma_0$ and $\Lambda:\mathbb{C}\to\mathbb{C}$ such that: $\Lambda$ is meromorphic on $\{\operatorname{Re} s>a\}$ for some $a<1$; for every $s$ with $\operatorname{Re} s>\sigma_0$ the family indexed by $v\notin S$ of the inverses of $P_v(N(v)^{-s})$, where $P_v$ is `rsEulerPoly` with arguments $a=\sigma.a\,v/\sigma.b\,v$, $b=(\sigma.b\,v)^{-1}$, $e_1=\tau.a\,v$, $e_2=\tau.b\,v$, $e_3=0$, i.e. $1-ae_1X+(a^2e_2+be_1^2-2be_2)X^2-abe_1e_2X^3+b^2e_2^2X^4$, has product $\Lambda(s)$; and if the meromorphic order of $\Lambda$ at $s=1$ is negative, then $\tau$ and $\sigma$ agree away from a finite set, i.e. $\tau.a\,v=\sigma.a\,v$ and $\tau.b\,v=\sigma.b\,v$ for all $v$ outside some finite set.
--
--   This is the Rankin–Selberg step in the form used here: meromorphic continuation of the partial $L$-function of the contragredient table of $\sigma$ against $\tau$ to a half-plane reaching past $s=1$, together with the rigidity statement that a pole at $s=1$ forces the two Hecke tables to coincide outside a finite set. It is stated for a single excluded set $S$, and is used to derive the version quantified over all sufficiently large excluded sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_lt_one_meromorphicOn_hasProd_rsEulerPoly_and_agreesAwayFromFinite_of_meromorphicOrderAt_one_neg.lean

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

theorem AutomorphicForm.exists_finset_lt_one_meromorphicOn_hasProd_rsEulerPoly_and_agreesAwayFromFinite_of_meromorphicOrderAt_one_neg
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (σ τ : HeckeEigensystem K ℂ)
    (hσ : IsArithGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) σ)
    (hτ : IsArithGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) τ)
    (hw : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ v ∉ S, ‖σ.b v‖ = ‖τ.b v‖) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
      (∃ a : ℝ, a < 1 ∧ MeromorphicOn Λ {s : ℂ | a < s.re}) ∧
      (∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (σ.a v.1 / σ.b v.1) (σ.b v.1)⁻¹
              (τ.a v.1) (τ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s)) ∧
      (meromorphicOrderAt Λ 1 < 0 → HeckeEigensystem.AgreesAwayFromFinite τ σ) := by sorry
