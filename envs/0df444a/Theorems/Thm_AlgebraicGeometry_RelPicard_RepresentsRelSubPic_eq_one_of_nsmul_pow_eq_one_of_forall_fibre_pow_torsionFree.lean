-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_eq_one_of_nsmul_pow_eq_one_of_forall_fibre_pow_torsionFree
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.eq_one_of_nsmul_pow_eq_one_of_forall_fibre_pow_torsionFree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/1da87486-1b03-5cbb-8de4-5afc41dd479d
-- title:
--   No p-power torsion among K-points of the representing scheme
-- statement:
--   Fix a scheme $C$ with a structure morphism $c\colon C\to\operatorname{Spec}\mathbb Z$ and a section $\varepsilon$ of $c$ (an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) c`, i.e. a morphism $\operatorname{Spec}\mathbb Z\to C$ whose composite with $c$ is the identity). Let $D$ be a `RelativePic0Designation ℤ c`, so in particular a scheme with structure morphism `D.toBase` over $\operatorname{Spec}\mathbb Z$ equipped with a zero section, and let $hD$ witness `RepresentsRelSubPic` for the cut `(algEquivZeroGroupCut c ε).toSubPicCondition`: that is, `D.toBase` carries a rigidified line bundle (the Poincaré bundle) on $C\times_{\mathbb Z}D$ lying in the cut `algEquivZeroCut c ε` (fibrewise algebraic equivalence to zero), such that for every $t\colon T\to\operatorname{Spec}\mathbb Z$ and every rigidified line bundle $M$ on $C\times_{\mathbb Z}T$ in the cut there is a unique morphism $g\colon T\to D$ over $\operatorname{Spec}\mathbb Z$ with $g^{*}$ of the Poincaré bundle isomorphic to $M$, the pullback along the zero section being isomorphic to the trivial rigidified bundle. Let $p$ be a natural number (primality is not assumed). The hypothesis `htors` states: for every field $K$ of characteristic $p$ that is algebraically closed and every $k\in\mathbb N$, the commutative group of in-cut classes of rigidified line bundles over $\operatorname{Spec} K$ — the set `(relSubPicPresheaf c ε _).obj (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))))` with the group law given by tensor product, the trivial bundle as unit and tensor-inverses — contains no element $\xi$ with $\xi^{p^{k}}=1$ other than $\xi=1$. The conclusion: for any such $K$, any $k$, and any $K$-point $x$ of $D$ over $\operatorname{Spec}\mathbb Z$, if the $p^{k}$-fold iterate `hD.relativeGroupLaw.nsmul _ (p ^ k) x` (the group law on points induced by representability) equals the neutral point, then $x$ is the neutral point.
--
--   The mathematical content is the transfer of a torsion-freeness statement for the relative Picard group, in the form used for $\mathrm{Pic}^{0}$ of curves over algebraically closed fields of characteristic $p$ (Bosch–Lütkebohmert–Raynaud), to the scheme representing the cut-out Picard subfunctor. In contrast to the textbook assertion about $\mathrm{Pic}^{0}$, nothing is proved here about line bundles: the statement is the formal consequence of representability, $p$ is an arbitrary natural number, and the genuine input is the hypothesis `htors` about classes of rigidified line bundles over algebraically closed fields of characteristic $p$. It is used in the construction of the good identity component of the Néron model attached to a Deligne–Rapoport model package, where quasi-finiteness of multiplication by $p^{k}$ on the special fibre is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_eq_one_of_nsmul_pow_eq_one_of_forall_fibre_pow_torsionFree.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.eq_one_of_nsmul_pow_eq_one_of_forall_fibre_pow_torsionFree
    {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of ℤ))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) c)
    (D : RelativePic0Designation ℤ c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D) (p : ℕ)

    (htors : ∀ (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (k : ℕ),
      letI := (algEquivZeroGroupCut c ε).commGroupObj (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))))
      ∀ ξ : (relSubPicPresheaf c ε (algEquivZeroGroupCut c ε).toSubPicCondition).obj
          (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))))), ξ ^ (p ^ k) = 1 → ξ = 1)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (k : ℕ)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))) D.toBase)
    (hx : hD.relativeGroupLaw.nsmul _ (p ^ k) x = hD.relativeGroupLaw.one _) :
    x = hD.relativeGroupLaw.one _ := by sorry
