-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_norm_foldr_archDerivAtComplex_le_of_mem_cut
-- name    : AutomorphicForm.CuspidalConstituent.exists_forall_norm_foldr_archDerivAtComplex_le_of_mem_cut
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/23c976c0-5629-5e47-810a-8e531037dbbc
-- title:
--   Iterated complex flow derivatives bounded on determinant slabs
-- statement:
--   Let $K$ be a number field and let $c,u,d_1,d_2$ be reals with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$ such that the union $\bigcup_{x\in T}(\cdot\, x)''$ of right translates of the centre-cut Siegel set $\mathrm{centreCutSiegelSet}\,K\,c\,u\,d_1\,d_2$ (finite part integral, all local heights $\ge c$, all $x$-window squares $\le u^2$, all archimedean determinant norms in $[d_1,d_2]$) satisfies `CoversModCentre`: every $g$ can be written, after left multiplication by a global point of $\mathrm{GL}_2(K)$ and right multiplication by a central idelic scalar, as an element of that union. Fix the production carrier data on this union, with level subgroups $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, Hecke generators $\mathrm{heckeGen}$ at the finite places, and the adelic box as conditioning set; its central subgroup is all of $(\mathbb{A}_K)^\times$, and $\xi$ is a homomorphism from it to $\mathbb{C}^\times$. Let $V$ be a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ which is a cuspidal constituent for these data and $\xi$, i.e. a nonzero cusp subrepresentation all of whose cusp subrepresentations are $0$ or $V$. Assume a real $w_0$ with $\|\xi(z)\|=\|z\|_{\mathbb{A}}^{w_0}$ for all ideles $z$; let $N\neq 0$ be an ideal of $\mathcal{O}_K$, let $\mathrm{tys}$ assign to each infinite place a finite family of archimedean types, and let $x$ lie in $V$, be invariant under right translation by $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, and lie in the archimedean type cut $\bigsqcap_w\bigsqcup_i$ of the type submodules given by $\mathrm{tys}$. Let $w$ be a complex infinite place of $K$, let $0<e_1<e_2$, and let $l$ be a finite list of the six flow directions $H,E,F,iH,iE,iF$ at $w$. Then there is a real $B$ such that for every $g$ with $\|\det g\|_{\mathbb{A}}\in[e_1,e_2]$ one has $\|(\,l\text{-fold iterate of }\mathrm{archDerivAtComplex}\ \text{applied to } x)(g)\|\le B$, where each operator sends $\varphi$ to $g\mapsto \frac{d}{dt}\varphi(g\cdot \mathrm{archFlowAtComplex}\,d\,t)|_{t=0}$. The proof discards the hypotheses $w_0$, $h\xi$ and $e_1<e_2$.
--
--   This is the regularity input, at all orders of differentiation, for the analytic manipulations with the archimedean flow derivatives at a complex place: boundedness of arbitrary iterated derivatives of a level-and-type cut vector of a cuspidal constituent on each slab $e_1\le\|\det g\|\le e_2$. It is used in the proofs of skew-symmetry of the six flow derivatives and of the relations between the two Casimir operators at a complex place, and in the lower bound for the real part of the Casimir eigenvalue on a highest-weight vector.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_forall_norm_foldr_archDerivAtComplex_le_of_mem_cut.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_forall_norm_foldr_archDerivAtComplex_le_of_mem_cut
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂) (l : List ArchDirComplex) :
    ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖(l.foldr (archDerivAtComplex hw) x) g‖ ≤ B := by sorry
