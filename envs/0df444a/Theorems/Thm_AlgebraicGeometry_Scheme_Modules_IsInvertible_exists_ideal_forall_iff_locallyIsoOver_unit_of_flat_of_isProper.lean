-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_iff_locallyIsoOver_unit_of_flat_of_isProper
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_ideal_forall_iff_locallyIsoOver_unit_of_flat_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/21102db1-1bb8-5cc3-841e-b85dda8f7e92
-- title:
--   See-saw: trivialisation locus is Spec(A/I), universally
-- statement:
--   Let $A$ be a Noetherian commutative ring, $X$ a scheme and $c : X \to \operatorname{Spec} A$ a proper flat morphism. Assume that for every commutative $A$-algebra $B$ the second projection $X \times_{\operatorname{Spec} A} \operatorname{Spec} B \to \operatorname{Spec} B$ induces a bijection on global sections of the structure sheaves. Let $N$ and $Ninv$ be $\mathcal{O}_X$-modules that are invertible in the sense that every point of $X$ has an open neighbourhood $U$ on which the pullback along $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules of $U$. Assume further: (i) for every field $K$ with an $A$-algebra structure, if the pullbacks of $N$ and of $Ninv$ along $X \times_{\operatorname{Spec} A} \operatorname{Spec} K \to X$ each admit a non-zero global section, then the pullback of $N$ there is isomorphic to the unit sheaf; (ii) for every scheme $Y$ and morphism $g : Y \to X$, if the pullback of $N$ along $g$ is isomorphic to the unit sheaf of $Y$, so is the pullback of $Ninv$. Then there is an ideal $I \subseteq A$ such that for every scheme $T'$ and every $\psi : T' \to \operatorname{Spec} A$, the morphism $\psi$ factors through $\operatorname{Spec}(A/I) \to \operatorname{Spec} A$ if and only if the pullback of $N$ along $X \times_{\operatorname{Spec} A} T' \to X$ is locally isomorphic over $T'$ to the unit sheaf, i.e. every point of $T'$ has an open neighbourhood $U$ over whose preimage in $X \times_{\operatorname{Spec} A} T'$ the two are isomorphic.
--
--   This is the see-saw theorem over an affine Noetherian base, in the form asserting that the locus where an invertible sheaf becomes trivial locally over the base is represented by the closed subscheme $\operatorname{Spec}(A/I)$, universally for all test schemes. It is the affine input to the version phrasing the conclusion as a closed immersion, which in turn feeds the construction of the relative Picard functor and of the Néron model infrastructure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ideal_forall_iff_locallyIsoOver_unit_of_flat_of_isProper.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_ideal_forall_iff_locallyIsoOver_unit_of_flat_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of A))
    [IsProper c] [Flat c]
    (hH0 : ∀ (B : Type u) [CommRing B] [Algebra A B],
      Function.Bijective (Limits.pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap A B)))).appTop)
    (N Ninv : X.Modules) (hN : Scheme.Modules.IsInvertible N) (hNinv : Scheme.Modules.IsInvertible Ninv)
    (hfib : ∀ (K : Type u) [Field K] [Algebra A K],
      (∃ s : Γ((Scheme.Modules.pullback
          (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap A K))))).obj N, ⊤), s ≠ 0) →
      (∃ t : Γ((Scheme.Modules.pullback
          (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap A K))))).obj Ninv, ⊤), t ≠ 0) →
        Nonempty ((Scheme.Modules.pullback
            (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap A K))))).obj N ≅
          SheafOfModules.unit (Limits.pullback c (Spec.map (CommRingCat.ofHom (algebraMap A K)))).ringCatSheaf))
    (hinv : ∀ (Y : Scheme.{u}) (g : Y ⟶ X),
      Nonempty ((Scheme.Modules.pullback g).obj N ≅ SheafOfModules.unit Y.ringCatSheaf) →
        Nonempty ((Scheme.Modules.pullback g).obj Ninv ≅ SheafOfModules.unit Y.ringCatSheaf)) :
    ∃ I : Ideal A, ∀ {T' : Scheme.{u}} (ψ : T' ⟶ Spec (CommRingCat.of A)),
      (∃ z : T' ⟶ Spec (CommRingCat.of (A ⧸ I)), z ≫ Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I))) = ψ) ↔
        Scheme.Modules.LocallyIsoOver (Limits.pullback.snd c ψ)
          ((Scheme.Modules.pullback (Limits.pullback.fst c ψ)).obj N)
          (SheafOfModules.unit (Limits.pullback c ψ).ringCatSheaf) := by sorry
