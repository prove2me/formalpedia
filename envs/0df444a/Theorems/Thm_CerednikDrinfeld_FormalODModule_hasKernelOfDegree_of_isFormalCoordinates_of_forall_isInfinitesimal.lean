-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_of_isFormalCoordinates_of_forall_isInfinitesimal
-- name    : CerednikDrinfeld.FormalODModule.hasKernelOfDegree_of_isFormalCoordinates_of_forall_isInfinitesimal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/a4398800-61db-5222-ab1e-7dfac6920217
-- title:
--   Degree d kernel algebra from infinitesimal n-torsion
-- statement:
--   Let $B$ be a Noetherian commutative ring, $A$ a scheme with a morphism $f : A \to \operatorname{Spec} B$, and $L$ a relative group law on $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \text{ lies over } t\}$ for $t : T \to \operatorname{Spec} B$, natural in $T$. Let $F$ be a $2$-dimensional formal group law over $B$ and let $\theta$ assign, to each $B$-algebra $B'$ and each pair $s \in (B')^2$, a point of $A$ over $\operatorname{Spec} B'$, such that $\theta$ are formal coordinates for $L$ with law $F$: $\theta$ is compatible with $B$-algebra maps on nilpotent tuples, and for every $B$-algebra $B'$ and ideal $J$ with $J^{k+1} = 0$ the map $s \mapsto \theta_{B'}(s)$ is a bijection from tuples with entries in $J$ onto the points that reduce to the unit section modulo $J$, carrying the truncated evaluation of $F$ to the multiplication of $L$. Let $\varphi = (\varphi_1,\varphi_2)$ be power series in two variables over $B$ with zero constant terms, and $n \ge 1$, such that for every $B$-algebra $B'$, every ideal $J$ with $J^{k+1} = 0$ and every $s$ with entries in $J$ one has $\theta_{B'}\big((\operatorname{nilEval} k\,\varphi_i\,s)_i\big) = n \cdot \theta_{B'}(s)$, the $n$-fold $L$-multiple. Assume further that the structural morphism $L.\mathrm{schemeKerStr}\ n$ of the kernel of multiplication by $n$, obtained as the pullback of the $n$-multiplication along the unit section, is finite, flat and locally of finite presentation, with $\operatorname{finrank}$ equal to a fixed $d$ at every point of $\operatorname{Spec} B$, and that every point $P$ of $A$ over a $B$-algebra $B'$ with $n \cdot P$ the unit is infinitesimal: there is a nilpotent ideal $J \subseteq B'$ modulo which $P$ becomes the unit section. Then `FormalODModule.HasKernelOfDegree φ d` holds: the kernel algebra `KerAlgebra φ` is a finite projective $B$-module, and for every field $\kappa$ and every ring homomorphism $B \to \kappa$ the $\kappa$-dimension of `KerAlgebra` of the base-changed $\varphi$ equals $d$.
--
--   This is the comparison between the kernel of multiplication by $n$ on a formal group law written in formal coordinates along the unit section and the $n$-torsion subscheme of the ambient relative group law: finiteness, local freeness and degree are transported from the $n$-torsion scheme to the algebra cut out by $\varphi$. It is used in the construction of the unique homomorphism lifting formal coordinates and, for the special formal modules over $\mathbb{Z}_{p^2}$, in the verification that the relevant kernel has degree four.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_of_isFormalCoordinates_of_forall_isInfinitesimal.lean

import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.hasKernelOfDegree_of_isFormalCoordinates_of_forall_isInfinitesimal
    {B : Type} [CommRing B] [IsNoetherianRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}
    (L : RelativeGroupLaw B f)
    (F : MvFormalGroup 2 B) (θ : RelativeGroupLaw.FormalCoordinates f 2) (hθ : L.IsFormalCoordinates F θ)
    (φ : Series B) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (n : ℕ) (hn : 0 < n)

    (hφ : ∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (k : ℕ), J ^ (k + 1) = ⊥ →
      ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
        θ B' (fun i => MvFormalGroup.nilEval k (φ i) s) = L.nsmul (Scheme.specOver (𝒪 := B) B') n (θ B' s))

    (d : ℕ) [IsFinite (L.schemeKerStr n)] [Flat (L.schemeKerStr n)] [LocallyOfFinitePresentation (L.schemeKerStr n)]
    (hrank : ∀ s : ↥(Spec (CommRingCat.of B)), (L.schemeKerStr n).finrank s = d)

    (hinf : ∀ (B' : Type) [CommRing B'] [Algebra B B'] (P : SchemeHomOver (Scheme.specOver (𝒪 := B) B') f),
      L.nsmul (Scheme.specOver (𝒪 := B) B') n P = L.one (Scheme.specOver (𝒪 := B) B') →
      ∃ J : Ideal B', IsNilpotent J ∧ L.IsInfinitesimal J P) :
    FormalODModule.HasKernelOfDegree φ d := by sorry
