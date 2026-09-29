-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_of_pullback_of_faithfullyFlat_of_isSeparated
-- name    : AlgebraicGeometry.Polarisation.LocIsoOnBase.of_pullback_of_faithfullyFlat_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/3844608a-237b-5796-b8e3-89fbdbe09aa6
-- title:
--   Local isomorphy over the base descends along faithfully flat base change
-- statement:
--   Let $S$ be a commutative ring and $S'$ a commutative $S$-algebra that is faithfully flat as an $S$-module. Let $A, A'$ be schemes, $f\colon A \to \operatorname{Spec} S$ a quasi-compact separated morphism, $f'\colon A' \to \operatorname{Spec} S'$ a morphism, and $g\colon A' \to A$ a morphism making the square formed by $g$, $f'$, $f$ and $\operatorname{Spec}$ of the structure map $S \to S'$ cartesian. Assume further that $f$ has trivial global sections universally: for every $S$-algebra $T$, the canonical map $T \to \Gamma(A \times_{\operatorname{Spec} S} \operatorname{Spec} T, \mathcal{O})$, the algebra structure being the one induced by the projection to $\operatorname{Spec} T$, is bijective. Let $\mathcal{L}, \mathcal{L}'$ be sheaves of modules on $A$ that are invertible in the project's sense, i.e. every point of $A$ has an open neighbourhood $U$ with the restriction of the module to $U$ isomorphic to the unit module sheaf of $U$. Suppose that $g^{*}\mathcal{L}$ and $g^{*}\mathcal{L}'$ are locally isomorphic over $\operatorname{Spec} S'$, meaning that every point $s \in \operatorname{Spec} S'$ has an open neighbourhood $U$ such that the restrictions of $g^{*}\mathcal{L}$ and $g^{*}\mathcal{L}'$ to the open subscheme $f'^{-1}(U)$ are isomorphic. Then $\mathcal{L}$ and $\mathcal{L}'$ are locally isomorphic over $\operatorname{Spec} S$ in the same sense: every point of $\operatorname{Spec} S$ has an open neighbourhood $U$ for which the restrictions of $\mathcal{L}$ and $\mathcal{L}'$ to $f^{-1}(U)$ are isomorphic.
--
--   This is the descent step for the equivalence relation "invertible modules that agree locally on the base", i.e. equality in the relative Picard group read locally on the base, along a faithfully flat extension of the base ring, under the hypothesis $f_*\mathcal{O} = \mathcal{O}$ universally. It is used in the treatment of polarisations: the statements that the kernel of the associated morphism is two-torsion and that the Rosati involution is compatible with base change both descend through it, as does the recognition of canonical polarisation data for fake elliptic curves after localisation at a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_of_pullback_of_faithfullyFlat_of_isSeparated.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Polarisation.LocIsoOnBase.of_pullback_of_faithfullyFlat_of_isSeparated
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {A A' : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) [QuasiCompact f] [IsSeparated f]
    (f' : A' ⟶ Spec (CommRingCat.of S')) (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (hH0 : ∀ (T : Type u) [CommRing T] [Algebra S T],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd f (Scheme.TwoAffineOpenCover.specMap S T)) ⊤
      Function.Bijective (algebraMap T Γ(pullback f (Scheme.TwoAffineOpenCover.specMap S T), ⊤)))
    (𝓛 𝓛' : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓛' : Scheme.Modules.IsInvertible 𝓛')
    (hiso : LocIsoOnBase f' ((Scheme.Modules.pullback g).obj 𝓛) ((Scheme.Modules.pullback g).obj 𝓛')) :
    LocIsoOnBase f 𝓛 𝓛' := by sorry
