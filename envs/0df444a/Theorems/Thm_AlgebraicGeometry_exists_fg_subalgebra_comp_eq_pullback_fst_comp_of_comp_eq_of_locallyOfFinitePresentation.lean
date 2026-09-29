-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_comp_eq_pullback_fst_comp_of_comp_eq_of_locallyOfFinitePresentation
-- name    : AlgebraicGeometry.exists_fg_subalgebra_comp_eq_pullback_fst_comp_of_comp_eq_of_locallyOfFinitePresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/3007f876-d45f-580e-9296-ed9c8256500e
-- title:
--   Spreading out a factorisation to a finitely generated subalgebra
-- statement:
--   Let $A_0$ be a commutative ring, $A$ a commutative $A_0$-algebra, and let $B$ be an $A_0$-subalgebra of $A$ that is finitely generated as an $A_0$-algebra. Let $X$, $W$, $V$ be schemes, let $f : X \to \operatorname{Spec} B$ be locally of finite type, let $w : W \to X$ be such that the composite of $w$ with $f$ is quasi-compact and quasi-separated, and let $v : V \to X$ be such that the composite of $v$ with $f$ is locally of finite presentation. Write $W \times_{\operatorname{Spec} B} \operatorname{Spec} A$ for the pullback of the structure morphism $W \to \operatorname{Spec} B$ (that is, $w$ followed by $f$) along the morphism $\operatorname{Spec} A \to \operatorname{Spec} B$ induced by the inclusion $B \hookrightarrow A$, and suppose given $a : W \times_{\operatorname{Spec} B} \operatorname{Spec} A \to V$ with $a$ followed by $v$ equal to the first projection followed by $w$, as morphisms to $X$. Then there exist a finitely generated $A_0$-subalgebra $T$ of $A$ with $B \le T$ and a morphism $a_T$ from the pullback of $W \to \operatorname{Spec} B$ along $\operatorname{Spec} T \to \operatorname{Spec} B$ (induced by the inclusion $B \le T$) to $V$, such that $a_T$ followed by $v$ equals the first projection followed by $w$. No compatibility between $a_T$ and the given $a$ is asserted.
--
--   This is a spreading-out statement in the style of EGA IV, §8: a factorisation through a morphism locally of finite presentation which exists after base change to the full algebra $A$ already exists after base change to some finitely generated intermediate stage $T$, the finitely generated $A_0$-subalgebras of $A$ containing $B$ forming a directed system with direct limit $A$. It is used in the study of fake elliptic curves in the Čerednik–Drinfeld setting, to descend to a finitely generated stage the containment of a kernel subscheme in the $2$-torsion, respectively in the unit section.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_fg_subalgebra_comp_eq_pullback_fst_comp_of_comp_eq_of_locallyOfFinitePresentation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_fg_subalgebra_comp_eq_pullback_fst_comp_of_comp_eq_of_locallyOfFinitePresentation
    {A₀ : Type} [CommRing A₀] {A : Type} [CommRing A] [Algebra A₀ A] (B : Subalgebra A₀ A) (hB : B.FG)
    {X W V : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of ↥B)) [LocallyOfFiniteType f]
    (w : W ⟶ X) [QuasiCompact (w ≫ f)] [QuasiSeparated (w ≫ f)]
    (v : V ⟶ X) [LocallyOfFinitePresentation (v ≫ f)]
    (a : pullback (w ≫ f) (Spec.map (CommRingCat.ofHom B.val.toRingHom)) ⟶ V)
    (ha : a ≫ v = pullback.fst (w ≫ f) (Spec.map (CommRingCat.ofHom B.val.toRingHom)) ≫ w) :
    ∃ (T : Subalgebra A₀ A) (_ : T.FG) (hle : B ≤ T)
      (aT : pullback (w ≫ f) (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom)) ⟶ V),
      aT ≫ v = pullback.fst (w ≫ f) (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom)) ≫ w := by sorry
