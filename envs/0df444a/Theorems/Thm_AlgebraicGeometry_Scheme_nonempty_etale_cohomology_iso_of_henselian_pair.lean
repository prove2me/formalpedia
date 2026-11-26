-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_cohomology_iso_of_henselian_pair
-- name    : AlgebraicGeometry.Scheme.nonempty_etale_cohomology_iso_of_henselian_pair
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-24T21:51:50.057989+00:00
-- url     : https://prove2.me/theorems/c845531d-d267-4719-8c96-b97cf6cf3afd
-- title:
--   Étale cohomology comparison for a henselian affine pair
-- statement:
--   Let $A\to B$ be surjective and let $(A,\ker(A\to B))$ be a henselian pair. For any abelian étale sheaf on $\operatorname{Spec}A$ killed by one positive integer, its cohomology agrees with that of its restriction to $\operatorname{Spec}B$. The closed subscheme can be given by any scheme isomorphic to $\operatorname{Spec}B$.
-- source:
--   Gabber's theorem, Stacks Project, Theorem 59.82.7, https://stacks.math.columbia.edu/tag/09ZI.

import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Mathlib.RingTheory.Henselian

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleSmallSite (pullbackSheaves)
universe u

theorem AlgebraicGeometry.Scheme.nonempty_etale_cohomology_iso_of_henselian_pair
    (A B : Type u) [CommRing A] [CommRing B] (r : A →+* B) [HenselianRing A (RingHom.ker r)]
    (_ : Function.Surjective r) {Z : Scheme.{u}} (e : Z ≅ Spec (.of B))
    (F : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u})
    (N : ℕ) (_ : N ≠ 0) (_ : N • 𝟙 F = 0) (q : ℕ) :
    Nonempty (AddCommGrpCat.of (F.H q) ≅
      AddCommGrpCat.of (((pullbackSheaves (e.hom ≫ Spec.map (CommRingCat.ofHom r))).obj F).H q)) := by sorry
