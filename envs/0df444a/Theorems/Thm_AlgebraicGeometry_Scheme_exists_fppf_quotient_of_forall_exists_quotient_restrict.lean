-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_fppf_quotient_of_forall_exists_quotient_restrict
-- name    : AlgebraicGeometry.Scheme.exists_fppf_quotient_of_forall_exists_quotient_restrict
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/134693d7-a9b9-5f23-9a04-45793d2edcab
-- title:
--   Gluing local effective fppf quotients of a relation
-- statement:
--   Let $X$ and $R$ be schemes and let $s, t : R \to X$ be two morphisms. Suppose given, for every point $x$ of $X$, an open subscheme $W x \subseteq X$ with $x \in W x$ whose two preimages agree, $s^{-1}(W x) = t^{-1}(W x)$ as open subsets of $R$; write $\iota_x$ for the resulting isomorphism $s^{-1}(W x) \cong t^{-1}(W x)$ of open subschemes. Suppose further that for each $x$ there exist a scheme $Y$ and a morphism $p : W x \to Y$ such that $p$ is flat, locally of finite presentation, quasi-compact and surjective, such that the restriction $s \mid_{W x} : s^{-1}(W x) \to W x$ and the composite of $\iota_x$ with $t \mid_{W x}$ become equal after composing with $p$, and such that these two morphisms exhibit $s^{-1}(W x)$ as the fibre product $W x \times_Y W x$ of $p$ with itself (the displayed equality is in any case part of the pullback condition). The conclusion is that there exist a scheme $Y$, a morphism $p : X \to Y$ and a proof $w$ that $s$ followed by $p$ equals $t$ followed by $p$, such that $p$ is flat, locally of finite presentation, quasi-compact and surjective, such that $s, t : R \to X$ exhibit $R$ as $X \times_Y X$, and such that the cofork of $p$ determined by $w$ is a colimit, i.e. $p$ is the coequaliser of $s$ and $t$ in the category of schemes.
--
--   This is the Zariski-local-to-global statement for effective fppf quotients of a relation $s, t : R \rightrightarrows X$: quotients existing over a saturated open neighbourhood of each point glue to a global one, which is moreover a coequaliser of schemes. It is used in the construction of the relative group law on Jacobians of curves of good reduction, via [`GoodReductionJacobian.RelativeGroupLaw.exists_fppf_quotient_isPullback_action_of_isClosedImmersion`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_fppf_quotient_isPullback_action_of_isClosedImmersion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_fppf_quotient_of_forall_exists_quotient_restrict.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_fppf_quotient_of_forall_exists_quotient_restrict
    {X R : Scheme.{u}} (s t : R ⟶ X)
    (W : X → X.Opens) (hxW : ∀ x, x ∈ W x) (hinv : ∀ x, s ⁻¹ᵁ W x = t ⁻¹ᵁ W x)
    (loc : ∀ x, ∃ (Y : Scheme.{u}) (p : (W x).toScheme ⟶ Y),
      (s ∣_ W x) ≫ p = ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) ≫ p ∧
      Flat p ∧ LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ Surjective p ∧
      IsPullback (s ∣_ W x) ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) p p) :
    ∃ (Y : Scheme.{u}) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      Flat p ∧ LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) := by sorry
