-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_casimirBar_eq_conj_and_sl2Invariant_of_casimir_eq_zero_of_isCuspConstituent_of_isComplex
-- name    : AutomorphicForm.CuspidalConstituent.casimirBar_eq_conj_and_sl2Invariant_of_casimir_eq_zero_of_isCuspConstituent_of_isComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/66b58fbb-2e44-53be-9319-dc6062babda5
-- title:
--   Casimir eigenvalues at a complex place: λ'=λ̄, spherical SL₂-invariance
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $0<c$, $0<d_1<d_2$, and let $T$ be a finite set of elements of $\mathrm{GL}_2$ of the adeles, such that the set $D=\bigcup_{x\in T}\{g x : g\in \mathrm{centreCutSiegelSet}\,K\,c\,u\,d_1\,d_2\}$ satisfies `CoversModCentre`: every $g$ admits $\gamma\in\mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g z\in D$. Work with the carrier data `productionPinsOf` attached to $D$, to the level subgroups $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, to the Hecke generators at finite places and to the adelic box; its central subgroup is all of the ideles, and $\xi$ is a homomorphism from it to $\mathbb{C}^\times$. Let $V$ be a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$ which is a cuspidal constituent for these data and $\xi$, i.e. a non-zero cusp subrepresentation admitting no proper non-zero cusp subrepresentation. Assume a non-zero ideal $N$ and an archimedean type family $tys$ are given for which the intersection of $V$ with the functions right-invariant under the level-$N$ subgroup and with the type cut $\mathrm{archCutSubmodule}(tys)$ is non-zero. Let $w$ be a complex infinite place, $w_0$ a real number with $\|\xi(z)\|=\mathrm{ideleNorm}(z)^{w_0}$ for all ideles $z$, and let $\lambda,\lambda'\in\mathbb{C}$ be such that every $x\in V$ is smooth at $w$ in the sense of `IsArchSmoothAtComplex`, has continuous first and second derivatives along all six flow directions $H,E,F,iH,iE,iF$ at $w$, and satisfies $\Omega x=\lambda x$, $\bar\Omega x=\lambda' x$, where $\Omega=-\bigl(\tfrac14\partial_H^2-\tfrac12\partial_H+\partial_E\partial_F\bigr)$ is formed from the Wirtinger-type operators $\mathrm{archDelAt}$ and $\bar\Omega$ from their conjugates $\mathrm{archDelBarAt}$. Then $\lambda'=\overline{\lambda}$; and if $\lambda=0$, then for every non-zero ideal $N'$, every archimedean type family $tys'$ and every $x$ lying in $V$, in the level-$N'$ invariants and in the type cut of $tys'$, such that the predicate `HasArchCharacterAt₀ K w 1 x` holds (trivial archimedean character at $w$), one has $x(g\cdot \mathrm{archComplexGLAt}\,h)=x(g)$ for all $g$ and all $h\in\mathrm{GL}_2(\mathbb{C})$ with $\det h=1$, where $\mathrm{archComplexGLAt}$ is the embedding of $\mathrm{GL}_2(\mathbb{C})$ into the adelic group at $w$ coming from an isomorphism $K_w\cong\mathbb{C}$.
--
--   This is the portion of unitarity of the archimedean component at a complex place that is needed downstream: self-adjointness of the Casimir pair for the Petersson pairing on a determinant slab forces the two eigenvalues to be complex conjugates, and in the degenerate case $\lambda=0$ the spherical vectors in the level-and-type cuts are right $\mathrm{SL}_2(K_w)$-invariant. It is used in the proof of the torus-decay bound for Whittaker coefficients at a complex place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_casimirBar_eq_conj_and_sl2Invariant_of_casimir_eq_zero_of_isCuspConstituent_of_isComplex.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent
open scoped ComplexConjugate

theorem AutomorphicForm.CuspidalConstituent.casimirBar_eq_conj_and_sl2Invariant_of_casimir_eq_zero_of_isCuspConstituent_of_isComplex
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
    (hX : V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ≠ ⊥)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (lam lam' : ℂ)
    (hlam : ∀ x ∈ V, IsArchSmoothAtComplex hw x ∧ (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x)) ∧
      (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) ∧
      archCasimirAtComplex hw x = lam • x ∧ archCasimirBarAtComplex hw x = lam' • x) :
    lam' = conj lam ∧
    (lam = 0 →
      ∀ (N' : Ideal (𝓞 K)), N' ≠ ⊥ → ∀ (tys' : AutomorphicForm.ArchTypeFamily K) (x : AdelicGL2 (𝓞 K) K → ℂ),
        x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N' ⊓ archCutSubmodule K tys' →
        HasArchCharacterAt₀ K w 1 x →
        ∀ (g : AdelicGL2 (𝓞 K) K) (h : GL (Fin 2) ℂ), Matrix.GeneralLinearGroup.det h = 1 →
          x (g * archComplexGLAt hw h) = x g) := by sorry
