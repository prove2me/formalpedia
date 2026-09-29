-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_forall_factors_iff_of_idealCut
-- name    : AlgebraicGeometry.exists_isClosedImmersion_forall_factors_iff_of_idealCut
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/0283e766-332a-5425-95d0-bfb692c4e997
-- title:
--   Representability of a closed subfunctor cut by local ideals
-- statement:
--   Let $H$ be a scheme and let $Q$ assign to every commutative ring $A$ (in the ambient universe) and every morphism $u : \operatorname{Spec} A \to H$ a proposition. Assume three hypotheses. First, `hQmap`: for all rings $A, A'$, every ring homomorphism $\varphi : A \to A'$ and every $u : \operatorname{Spec} A \to H$, if $Q\,A\,u$ holds then so does $Q\,A'$ of $\operatorname{Spec}(\varphi)$ followed by $u$. Second, `hQloc`: for every $A$, every $u : \operatorname{Spec} A \to H$ and every family $r : \iota \to A$ whose range spans the unit ideal, if $Q$ holds of the composite $\operatorname{Spec}(A[1/r_i]) \to \operatorname{Spec} A \xrightarrow{u} H$ for each $i$ (with $A[1/r_i]$ the away localisation), then $Q\,A\,u$ holds. Third, `hQcut`: for every open $U \subseteq H$ that is affine, every ring $B$ and every isomorphism $e : \operatorname{Spec} B \cong U$, there is an ideal $J \subseteq B$ such that for all rings $A$ and all $\varphi : B \to A$, $Q\,A$ of $\operatorname{Spec}(\varphi)$ followed by $e$ and the inclusion $U \hookrightarrow H$ holds if and only if $\varphi(J)$ generates the zero ideal of $A$. The conclusion: there exist a scheme $C$ and a closed immersion $\iota : C \to H$ such that for every ring $A$ and every $u : \operatorname{Spec} A \to H$, the morphism $u$ factors as $v$ followed by $\iota$ for some $v : \operatorname{Spec} A \to C$ if and only if $Q\,A\,u$ holds.
--
--   This is the criterion that a subfunctor of a scheme which is Zariski-local on the test ring and is cut out, over each affine open, by the vanishing of an ideal is represented by a closed subscheme. It is used in the form with finite presentation added, [`AlgebraicGeometry.exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_of_fg_idealCut`](thm.html#AlgebraicGeometry.exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_of_fg_idealCut).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isClosedImmersion_forall_factors_iff_of_idealCut.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_isClosedImmersion_forall_factors_iff_of_idealCut
    (H : Scheme.{u})
    (Q : ∀ (A : Type u) [CommRing A], (Spec (CommRingCat.of A) ⟶ H) → Prop)

    (hQmap : ∀ (A A' : Type u) [CommRing A] [CommRing A'] (φ : A →+* A') (u : Spec (CommRingCat.of A) ⟶ H),
      Q A u → Q A' (Spec.map (CommRingCat.ofHom φ) ≫ u))

    (hQloc : ∀ (A : Type u) [CommRing A] (u : Spec (CommRingCat.of A) ⟶ H) (ι : Type u) (r : ι → A),
      Ideal.span (Set.range r) = ⊤ →
      (∀ i, Q (Localization.Away (r i))
        (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (r i)))) ≫ u)) → Q A u)

    (hQcut : ∀ (U : H.Opens) (hU : IsAffineOpen U) (B : Type u) [CommRing B]
      (e : Spec (CommRingCat.of B) ≅ (U : Scheme.{u})),
      ∃ J : Ideal B, ∀ (A : Type u) [CommRing A] (φ : B →+* A),
        Q A (Spec.map (CommRingCat.ofHom φ) ≫ e.hom ≫ U.ι) ↔ Ideal.map φ J = ⊥) :
    ∃ (C : Scheme.{u}) (ι : C ⟶ H), IsClosedImmersion ι ∧
      ∀ (A : Type u) [CommRing A] (u : Spec (CommRingCat.of A) ⟶ H),
        (∃ v : Spec (CommRingCat.of A) ⟶ C, v ≫ ι = u) ↔ Q A u := by sorry
