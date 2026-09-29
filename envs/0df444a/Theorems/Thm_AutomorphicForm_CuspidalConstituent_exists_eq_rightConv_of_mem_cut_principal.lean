-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_eq_rightConv_of_mem_cut_principal
-- name    : AutomorphicForm.CuspidalConstituent.exists_eq_rightConv_of_mem_cut_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/ad9ebbe2-13f1-5cba-adf7-d02c7416fbaf
-- title:
--   Smoothing vectors of a level-and-type cut, principal level
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Put $D=\bigcup_{t\in T}\{g t : g\in S\}$, where $S$ is the centre-cut Siegel set of parameters $c,u,d_1,d_2$: the $g$ whose finite part lies in the integral points, whose archimedean components have local height at least $c$ and squared $x$-window at most $u^2$ at every infinite place, and whose archimedean determinant norms all lie in $[d_1,d_2]$. Assume $D$ covers modulo the centre, i.e. every $g$ satisfies $\gamma g z\in D$ for some $\gamma\in \mathrm{GL}_2(K)$ and some central adelic scalar $z$. Fix the production carrier data on $D$ with level family $N\mapsto K(N)\cap\ker(\text{archimedean projection})$ (the principal level met with the finite-adelic subgroup), Hecke generators $\mathrm{heckeGen}$ and the adelic box, a character $\xi$ of its central subgroup, and a submodule $V\subseteq(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ that is a cuspidal constituent for these data: $V$ is a nonzero cuspidal subrepresentation with no cuspidal subrepresentation other than $0$ and $V$. Let $N\neq 0$ be an ideal of $\mathcal O_K$, let $\mathrm{tys}$ assign to each infinite place $w$ a number $\mathrm{card}\,w$ of archimedean representations $\mathrm{rep}\,w\,i$, and let $x$ lie in the cut $X=V\cap\{\varphi:\varphi(gu)=\varphi(g)\ \forall g,\ \forall u\in K(N)\cap\ker\}\cap\bigcap_w\sum_i\,(\text{the }\mathrm{rep}\,w\,i\text{-type submodule at }w)$. Then there exist $x'\in X$ and a function $\alpha$ on $\mathrm{GL}_2(\mathbb{A}_K)$ which factorises as an archimedean test factor times a finite test factor, satisfies $(y\mapsto\alpha(y^{-1}))\in\mathrm{archCutSubmodule}$ and $\alpha\in\mathrm{archDualCutSubmodule}$ for $\mathrm{tys}$, and is invariant under left and right translation by $K(N)\cap\ker$, such that $x(g)=\int\alpha(y)\,x'(gy)\,dy$ against the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, for all $g$.
--
--   This is the smoothing (approximate identity) step for $\mathrm{GL}_2$ over a number field at principal level: every vector of a level-and-type cut of a cuspidal constituent is a right convolution of another vector of the same cut against an admissible bi-finite test function. It feeds the statements that vectors in such a cut are archimedean-smooth with continuous derivatives and Casimir images in the cut.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_eq_rightConv_of_mem_cut_principal.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_eq_rightConv_of_mem_cut_principal
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys) :
    ∃ x' : AdelicGL2 (𝓞 K) K → ℂ, x' ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ∧
    ∃ α : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K α ∧ IsArchBiFinite K tys α ∧
      (∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), α (k * g) = α g ∧ α (g * k) = α g) ∧
      x = rightConv K x' α := by sorry
