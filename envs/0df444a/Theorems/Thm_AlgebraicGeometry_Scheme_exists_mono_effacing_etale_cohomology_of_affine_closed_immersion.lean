-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_mono_effacing_etale_cohomology_of_affine_closed_immersion
-- name    : AlgebraicGeometry.Scheme.exists_mono_effacing_etale_cohomology_of_affine_closed_immersion
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-24T22:44:06.26543+00:00
-- url     : https://prove2.me/theorems/e1aae950-fe28-4bce-b7b9-fadf4996aaa4
-- title:
--   Effacing an étale cohomology class on an affine closed fiber with bounded torsion coefficients
-- statement:
--   Let $i:Zhookrightarrow X$ be a closed immersion into an affine scheme, and let $F$ be an abelian étale sheaf on $X$ killed by a positive integer $N$. Each positive-degree class of $i^*F$ can be killed by a monomorphism $F	o G$ of étale sheaves on $X$ with $G$ also killed by $N$.
-- source:
--   Bounded-coefficient version of Stacks Project, Lemma 59.82.1, https://stacks.math.columbia.edu/tag/09ZE.

import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts
import Mathlib.RingTheory.Henselian

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtaleSmallSite (pullbackSheaves)
universe u

theorem AlgebraicGeometry.Scheme.exists_mono_effacing_etale_cohomology_of_affine_closed_immersion
    {X Z : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i]
    (N : ℕ) (_ : N ≠ 0) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (_ : N • 𝟙 F = 0)
    (q : ℕ) (x : ((pullbackSheaves i).obj F).H (q + 1)) :
    ∃ (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (a : F ⟶ G),
      Mono a ∧ N • 𝟙 G = 0 ∧ Sheaf.H.map ((pullbackSheaves i).map a) (q + 1) x = 0 := by sorry
