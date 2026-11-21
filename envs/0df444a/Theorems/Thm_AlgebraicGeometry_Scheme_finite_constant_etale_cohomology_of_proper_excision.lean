-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_finite_constant_etale_cohomology_of_proper_excision
-- name    : AlgebraicGeometry.Scheme.finite_constant_etale_cohomology_of_proper_excision
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-20T19:21:25.221188+00:00
-- url     : https://prove2.me/theorems/ffd32e74-9b3d-4ab4-a1ee-fd5cc805c300
-- title:
--   Étale cohomology finiteness descends across a proper excision square
-- statement:
--   Let $f\colon Y\to X$ be proper and $i\colon Z\hookrightarrow X$ be a closed immersion. Suppose $f$ is an isomorphism over the open complement of the image of $Z$, and write $E=Y\times_X Z$. For a finite abelian group $A$, assume that
--   $$H^q_{\mathrm{et}}(Y,\underline A),\qquad H^q_{\mathrm{et}}(Z,\underline A),\qquad H^q_{\mathrm{et}}(E,\underline A)$$
--   are finite in every degree. Then $H^q_{\mathrm{et}}(X,\underline A)$ is finite in every degree. This is the finiteness implication for a proper excision square, including a blowup square.
-- source:
--   Finiteness consequence of the proof of Stacks Project, Lemmas 59.105.1 and 59.105.2 (https://stacks.math.columbia.edu/tag/0EW4), using proper base change (Theorem 59.91.11, https://stacks.math.columbia.edu/tag/095T) for an abstract blowup square.

import Mathlib

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem AlgebraicGeometry.Scheme.finite_constant_etale_cohomology_of_proper_excision
    (A : Type u) [AddCommGroup A] [Finite A] {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) [IsIso (f ∣_ U)] (hU : Set.range i = (U : Set X)ᶜ)
    (hY : ∀ q, Finite (((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H q)) (hZ : ∀ q, Finite (((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H q))
    (hE : ∀ q, Finite (((constantSheaf (pullback f i).smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H q)) (q : ℕ) :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H q) := by sorry
