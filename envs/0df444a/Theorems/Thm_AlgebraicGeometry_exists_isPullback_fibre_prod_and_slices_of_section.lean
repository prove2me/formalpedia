-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isPullback_fibre_prod_and_slices_of_section
-- name    : AlgebraicGeometry.exists_isPullback_fibre_prod_and_slices_of_section
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/a041e7ac-1f69-53df-a25f-0d24cb747169
-- title:
--   Base change of A×_S A along S→ K, with slices
-- statement:
--   Let $r\colon S\to K$ be a homomorphism of commutative rings, let $A$ be a scheme, let $f\colon A\to\operatorname{Spec} S$ be a separated morphism, and let $e\colon\operatorname{Spec} S\to A$ satisfy $e$ followed by $f$ equals the identity, i.e. $e$ is a section of $f$. Let $a_K\colon A_K\to A$ and $x_K\colon A_K\to\operatorname{Spec} K$ form a cartesian square over $f$ and $\operatorname{Spec}(r)$. Write $P=\operatorname{pullback} f\,f$ with structure morphism $q_P=\mathrm{pr}_1$ followed by $f$, and $P_K=\operatorname{pullback} q_P\,\operatorname{Spec}(r)$, with projections $\pi_P\colon P_K\to P$ and $\pi_K\colon P_K\to\operatorname{Spec} K$. The assertion is that there exist morphisms $p_1,p_2\colon P_K\to A_K$, a morphism $e_K\colon\operatorname{Spec} K\to A_K$, and morphisms $i_X,i_Y\colon A_K\to P_K$ such that: $p_1$ followed by $a_K$ equals $\pi_P$ followed by $\mathrm{pr}_1$, and $p_2$ followed by $a_K$ equals $\pi_P$ followed by $\mathrm{pr}_2$, while both $p_1$ and $p_2$ followed by $x_K$ equal $\pi_K$; the square formed by $p_1,p_2$ over $x_K,x_K$ is cartesian, so $P_K$ is $A_K\times_K A_K$; $e_K$ followed by $a_K$ equals $\operatorname{Spec}(r)$ followed by $e$, and $e_K$ followed by $x_K$ is the identity; $i_X$ and $i_Y$ are closed immersions with $i_X$ followed by $p_1$ the identity of $A_K$ and $i_X$ followed by $p_2$ equal to $x_K$ followed by $e_K$, and symmetrically $i_Y$ followed by $p_1$ equal to $x_K$ followed by $e_K$ and $i_Y$ followed by $p_2$ the identity; finally $i_X$ followed by $\pi_P$ equals $a_K$ followed by the morphism $A\to P$ with components $(\mathrm{id}_A,\,f\text{ then }e)$, and $i_Y$ followed by $\pi_P$ equals $a_K$ followed by the morphism $A\to P$ with components $(f\text{ then }e,\,\mathrm{id}_A)$.
--
--   This is the base-change bookkeeping identifying the fibre over $\operatorname{Spec} K$ of the self-product $A\times_S A$ with $A_K\times_K A_K$, together with the unit section and the two slices $(\mathrm{id},e_K)$, $(e_K,\mathrm{id})$ realised as closed immersions compatible with the slices $(\mathrm{id}_A,f\circ e)$, $(f\circ e,\mathrm{id}_A)$ of $A\to A\times_S A$. It supplies the standard package of data used by the lifting steps for a relative group law, [`GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_of_isPullback_of_ker_mul_maximalIdeal_eq_bot`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_of_isPullback_of_ker_mul_maximalIdeal_eq_bot) and [`GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_of_smallExtension`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_of_smallExtension).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isPullback_fibre_prod_and_slices_of_section.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isPullback_fibre_prod_and_slices_of_section
    {S K : Type u} [CommRing S] [CommRing K] (r : S →+* K)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) [IsSeparated f]
    (e : Spec (CommRingCat.of S) ⟶ A) (he : e ≫ f = 𝟙 _)
    {AK : Scheme.{u}} (aK : AK ⟶ A) (xK : AK ⟶ Spec (CommRingCat.of K))
    (haK : IsPullback aK xK f (Spec.map (CommRingCat.ofHom r))) :
    ∃ (p₁ p₂ : pullback (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r)) ⟶ AK)
      (eK : Spec (CommRingCat.of K) ⟶ AK)
      (iX iY : AK ⟶ pullback (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r))),
      p₁ ≫ aK = pullback.fst (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r)) ≫ pullback.fst f f ∧
      p₁ ≫ xK = pullback.snd (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r)) ∧
      p₂ ≫ aK = pullback.fst (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r)) ≫ pullback.snd f f ∧
      p₂ ≫ xK = pullback.snd (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r)) ∧
      IsPullback p₁ p₂ xK xK ∧
      eK ≫ aK = Spec.map (CommRingCat.ofHom r) ≫ e ∧ eK ≫ xK = 𝟙 _ ∧
      IsClosedImmersion iX ∧ iX ≫ p₁ = 𝟙 AK ∧ iX ≫ p₂ = xK ≫ eK ∧
      iX ≫ pullback.fst (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r))
        = aK ≫ pullback.lift (𝟙 A) (f ≫ e) (by rw [Category.id_comp, Category.assoc, he, Category.comp_id]) ∧
      IsClosedImmersion iY ∧ iY ≫ p₁ = xK ≫ eK ∧ iY ≫ p₂ = 𝟙 AK ∧
      iY ≫ pullback.fst (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r))
        = aK ≫ pullback.lift (f ≫ e) (𝟙 A) (by rw [Category.id_comp, Category.assoc, he, Category.comp_id]) := by sorry
