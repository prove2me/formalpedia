-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_etale_geometric_fiber_comparison_of_projective_projection
-- name    : AlgebraicGeometry.Scheme.exists_etale_geometric_fiber_comparison_of_projective_projection
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-24T00:42:10.210783+00:00
-- url     : https://prove2.me/theorems/e030f186-cde7-42ea-a1e6-7350e6c39edd
-- title:
--   Étale stalk comparison with sections on a projective geometric fiber
-- statement:
--   Let $r\colon P\to S$ be a base change of a projective-space projection and let $s\colon\operatorname{Spec}K\to S$ with $K$ algebraically closed. For an abelian étale sheaf $F$ on $P$, the geometric stalk $(r_*F)_s$ is isomorphic to the group of global sections of the inverse image of $F$ on $P_s$. The comparison takes evaluation at a $K$-point of $P_s$ to evaluation of the original direct-image stalk at the induced point of $P$.
-- source:
--   Stacks Project, Lemma 59.91.4, https://stacks.math.columbia.edu/tag/0A3T.

import Definitions.Def_AlgebraicGeometry_EtaleDirectImageSectionGerms
import Definitions.Def_AlgebraicGeometry_EtaleStrictHenselianSectionGerms
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleDirectImageGerms (evalAtLiftOver)
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtaleStalkPullback (stalkPullbackIso)
open PhilipponStrictHenselianEtaleCohomology (terminalGerm)
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.exists_etale_geometric_fiber_comparison_of_projective_projection
    (R : Type u) [CommRing R] (n : ℕ) {P S : Scheme.{u}}
    (v : S ⟶ Spec (.of R))
    (a : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) (r : P ⟶ S)
    (h : IsPullback a r (ProjSpace.π R n) v) :
    ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S)
      {T : Scheme.{u}} (j : T ⟶ Spec (.of K)) (d : T ⟶ P) (h' : IsPullback j d s r)
      (F : Sheaf P.smallEtaleTopology AddCommGrpCat.{u}),
      ∃ e : (Scheme.pointSmallEtale s).sheafFiber.obj ((pushforward r).obj F) ≅
          (globalSections T).obj ((pullbackSheaves d).obj F),
        ∀ (w : Spec (.of K) ⟶ T) (hw : w ≫ j = 𝟙 _),
          e.hom ≫ (terminalGerm w).app ((pullbackSheaves d).obj F) ≫ (stalkPullbackIso d w).hom.app F =
            evalAtLiftOver r (w ≫ d) s
              (by rw [Category.assoc, ← h'.w, ← Category.assoc, hw, Category.id_comp]) F := by sorry
