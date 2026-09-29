-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_intermediateField_isInvertible_nonempty_pullback_iso_of_isAlgebraic
-- name    : AlgebraicGeometry.Scheme.Modules.exists_intermediateField_isInvertible_nonempty_pullback_iso_of_isAlgebraic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/ec6e984d-cb6b-518f-b5b7-15e67c695d91
-- title:
--   Invertible sheaves over an algebraic extension descend to a finite subextension
-- statement:
--   Let $K$ and $\bar K$ be fields in the smallest universe, with $\bar K$ a $K$-algebra that is algebraic over $K$, let $X$ be a scheme and let $fX : X \to \operatorname{Spec} K$ be a morphism that is quasi-compact and quasi-separated. Let $\mathcal L$ be a sheaf of modules on the fibre product $X \times_{\operatorname{Spec} K} \operatorname{Spec} \bar K$, formed as the categorical pullback of $fX$ along $\operatorname{Spec}$ of the structure map $K \to \bar K$, and assume $\mathcal L$ is invertible in the sense of the project predicate `Scheme.Modules.IsInvertible`: every point of the pullback scheme has an open neighbourhood $U$ such that the restriction of $\mathcal L$ along the inclusion $U \hookrightarrow X\times_K\operatorname{Spec}\bar K$ is isomorphic to the unit sheaf of modules of $U$. Then there exist an intermediate field $K \subseteq F \subseteq \bar K$ with $F$ finite-dimensional over $K$ and a sheaf of modules $\mathcal L_F$ on the pullback of $fX$ along $\operatorname{Spec}(K \to F)$, again invertible in the same local sense, such that for every morphism $c : X\times_K\operatorname{Spec}\bar K \to X\times_K\operatorname{Spec} F$ whose composite with the first projection is the first projection, and whose composite with the second projection equals the second projection followed by $\operatorname{Spec}(F \to \bar K)$, the pullback $c^{*}\mathcal L_F$ is isomorphic to $\mathcal L$ (the type of such isomorphisms is nonempty). Note that the comparison morphism $c$ is quantified over rather than produced.
--
--   This is the standard spreading-out statement that an invertible sheaf on a quasi-compact quasi-separated scheme base-changed to an algebraic extension $\bar K$ of $K$ is already defined over a finite subextension (EGA IV 8.5). It is used in the construction of fake elliptic curves attached to quaternionic data, where a line bundle over an algebraic closure must be realised over a finite extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_intermediateField_isInvertible_nonempty_pullback_iso_of_isAlgebraic.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_intermediateField_isInvertible_nonempty_pullback_iso_of_isAlgebraic
    (K Kbar : Type) [Field K] [Field Kbar] [Algebra K Kbar] [Algebra.IsAlgebraic K Kbar]
    {X : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of K)) [QuasiCompact fX] [QuasiSeparated fX]
    (𝓛 : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap K Kbar)))).Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) :
    ∃ (F : IntermediateField K Kbar) (_ : FiniteDimensional K F)
      (𝓛F : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap K F)))).Modules),
      Scheme.Modules.IsInvertible 𝓛F ∧
      ∀ cX : Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap K Kbar))) ⟶
          Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap K F))),
        cX ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K F))) =
          Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K Kbar))) →
        cX ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap K F))) =
          Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap K Kbar))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap F Kbar)) →
        Nonempty ((Scheme.Modules.pullback cX).obj 𝓛F ≅ 𝓛) := by sorry
