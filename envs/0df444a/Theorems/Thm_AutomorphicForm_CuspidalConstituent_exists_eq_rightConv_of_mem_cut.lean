-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_eq_rightConv_of_mem_cut
-- name    : AutomorphicForm.CuspidalConstituent.exists_eq_rightConv_of_mem_cut
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/7fa98eb6-22bd-5d22-9c43-e3febbc9a15a
-- title:
--   Vectors of level-and-type cuts are right convolutions
-- statement:
--   Let $K$ be a number field and let $c,u,d_1,d_2$ be reals with $c>0$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Put $D=\bigcup_{x\in T}(\cdot\;x)\big(\,\mathrm{centreCutSiegelSet}\,K\,c\,u\,d_1\,d_2\big)$, the union of the right translates by the elements of $T$ of the set of $g$ whose finite part is integral, whose archimedean components have local height at least $c$ and squared $x$-window at most $u^2$ at every infinite place, and whose archimedean determinant norms all lie in $[d_1,d_2]$; assume $D$ covers modulo the centre, i.e. every $g$ admits $\gamma\in\mathrm{GL}_2(K)$ and an idele unit $z$ with $\gamma g\,z\in D$. Consider the carrier data `productionPinsOf` attached to $D$, to the level subgroups $N\mapsto\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, to the Hecke generators at the finite places and to `adelicBox`, let $\xi$ be a character of its central subgroup, and let $V$ be a submodule of $\mathbb{C}$-valued functions on $\mathrm{GL}_2(\mathbb{A}_K)$ which is a cuspidal constituent for these data and $\xi$: a nonzero cuspidal subrepresentation all of whose cuspidal subrepresentations are $\bot$ or $V$. Let $N\neq0$ be an ideal of $\mathcal{O}_K$, let $\mathrm{tys}$ assign to each infinite place $w$ a finite list of archimedean types, and write $X$ for the intersection of $V$ with the submodule of functions right-invariant under $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$ and with the type cut $\bigsqcap_w\bigsqcup_i$ of the corresponding archimedean type submodules. Then for every $x\in X$ there are $x'\in X$ and a function $\alpha$ on $\mathrm{GL}_2(\mathbb{A}_K)$ which is a factorizable test function (a product of an archimedean test factor in the archimedean component and a finite test factor in the finite component), archimedean bi-finite of type $\mathrm{tys}$ (that is, $g\mapsto\alpha(g^{-1})$ lies in the type cut and $\alpha$ lies in the dual type cut), and two-sided invariant under $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, such that $x=\mathrm{rightConv}\,x'\,\alpha$, i.e. $x(g)=\int x'(gy)\,\alpha(y)\,d\mu(y)$ for the adelic Haar measure $\mu$ on $\mathrm{GL}_2(\mathbb{A}_K)$.
--
--   This is the easy, $K$-finite and finite-dimensional case of a Dixmier–Malliavin-type factorisation: every vector of a level-and-type cut of a cuspidal constituent is the right convolution of another vector of the same cut with an admissible bi-finite test function. It is used to transfer analytic properties of test functions to the vectors themselves, for instance in the bounds for iterated archimedean derivatives and in the construction of raising and lowering operators on such cuts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_eq_rightConv_of_mem_cut.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_eq_rightConv_of_mem_cut
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
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys) :
    ∃ x' : AdelicGL2 (𝓞 K) K → ℂ, x' ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ∧
    ∃ α : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K α ∧ IsArchBiFinite K tys α ∧
      (∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), α (k * g) = α g ∧ α (g * k) = α g) ∧
      x = rightConv K x' α := by sorry
