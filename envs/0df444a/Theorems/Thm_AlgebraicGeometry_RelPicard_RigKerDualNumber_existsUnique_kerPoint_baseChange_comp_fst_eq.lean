-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq
-- name    : AlgebraicGeometry.RelPicard.RigKerDualNumber.existsUnique_kerPoint_baseChange_comp_fst_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/069cae05-717a-55ea-8bf2-7269beb07e42
-- title:
--   Unique lift of a unit-reducing dual-number point under base change
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme, $c\colon C\to\operatorname{Spec}R$, and $\varepsilon$ a section of $c$ (a morphism $\operatorname{Spec}R\to C$ composing with $c$ to the identity). Let $D$ consist of a scheme $D.P$ with a structure morphism `D.toBase` to $\operatorname{Spec}R$ and a zero section, and let $h$ witness that $D$ represents the rigidified Picard functor cut out by `algEquivZeroCut c ε` (rigidified line bundles on $C\times_R T$ that are fibrewise algebraically equivalent to zero): a Poincaré bundle on $C\times_R D.P$ in the class, with the universal property that every such bundle over $T$ is the pullback of the Poincaré bundle along a unique $T$-point of $D.P$ over $\operatorname{Spec}R$, trivial along the zero section. Let $R'$ be an $R$-algebra, let $h'$ be the corresponding representability statement for the base change $C\times_R\operatorname{Spec}R'\to\operatorname{Spec}R'$, its induced section, the corresponding condition and $D.baseChange\,R'=(D.P\times_{\operatorname{Spec}R}\operatorname{Spec}R',\ \mathrm{pr}_2)$, and assume $hP$: the Poincaré bundle of $h'$ is isomorphic to the transport under `BaseChange.ofR` of the pullback of the Poincaré bundle of $h$ along $\mathrm{pr}_1\colon D.P\times_{\operatorname{Spec}R}\operatorname{Spec}R'\to D.P$. Let $B$ be a commutative ring that is an $R$- and $R'$-algebra with $R\to R'\to B$ a scalar tower, and write $B[\epsilon]$ for the dual numbers $\mathrm{DualNumber}\,B$. Let $x$ be a morphism $\operatorname{Spec}B[\epsilon]\to D.P$ over $\operatorname{Spec}R$ whose composition with the reduction $\operatorname{Spec}B\to\operatorname{Spec}B[\epsilon]$ induced by $B[\epsilon]\to B$ equals the unit point of the relative group law attached to $h$ at $\operatorname{Spec}B$. Then there is a unique morphism $x'\colon\operatorname{Spec}B[\epsilon]\to D.P\times_{\operatorname{Spec}R}\operatorname{Spec}R'$ over $\operatorname{Spec}R'$ whose composition with the reduction $\operatorname{Spec}B\to\operatorname{Spec}B[\epsilon]$ over $R'$ is the unit point of the relative group law attached to $h'$ at $\operatorname{Spec}B$, and which satisfies $\mathrm{pr}_1\circ x'=x$.
--
--   This is the base-change comparison for the kernel of the dual-number reduction on the representing scheme of the relative $\mathrm{Pic}^0$: points with values in $B[\epsilon]$ reducing to the unit descend uniquely across $\operatorname{Spec}R'\to\operatorname{Spec}R$, so that such kernel points over $R$ and over $R'$ correspond. It feeds the deformation-class computation [`AlgebraicGeometry.RelPicard.IsDeformationClassMap.exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_mono`](thm.html#AlgebraicGeometry.RelPicard.IsDeformationClassMap.exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_mono), and its proof uses the compatibility of the two relative group laws under $\mathrm{pr}_1$ recorded in [`AlgebraicGeometry.RelPicard.baseChange_relativeGroupLaw_mul_compat`](thm.html#AlgebraicGeometry.RelPicard.baseChange_relativeGroupLaw_mul_compat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RigKerDualNumberBaseTransport
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.RigKerDualNumber.existsUnique_kerPoint_baseChange_comp_fst_eq
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    (B : Type u) [CommRing B] [Algebra R' B] [Algebra R B] [IsScalarTower R R' B]
    (x : { x : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap R (DualNumber B)) D.toBase //
      dualNumberReduction R B ≫ x.1 =
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one
          (Scheme.TwoAffineOpenCover.specMap R B)).1 })
    : ∃! x' : { x' : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap R' (DualNumber B)) (D.baseChange R').toBase //
      dualNumberReduction R' B ≫ x'.1 =
        ((RepresentsRelSubPic.relativeGroupLaw
          (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h').one
          (Scheme.TwoAffineOpenCover.specMap R' B)).1 },
      x'.1.1 ≫ pullback.fst D.toBase (specMap R R') = x.1.1 := by sorry
