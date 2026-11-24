-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_subsingleton_etale_cohomology_restrict_injective_module_closed_fiber_prime
-- name    : AlgebraicGeometry.Scheme.subsingleton_etale_cohomology_restrict_injective_module_closed_fiber_prime
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-23T22:02:19.392796+00:00
-- url     : https://prove2.me/theorems/5056f508-1cd5-4ac4-8778-55c92d1311ef
-- title:
--   Closed-fiber acyclicity for injective étale sheaves with prime field coefficients
-- statement:
--   Let $Y$ be proper over a strictly henselian local ring, with closed fiber inclusion $i$. For a prime $\ell$ and an injective sheaf of $\mathbf Z/\ell\mathbf Z$-modules on $Y_{\acute{e}tale}$, the restriction of its underlying abelian sheaf to the closed fiber has zero positive-degree étale cohomology.
-- source:
--   Stacks Project, Lemma 59.91.6 and Theorem 59.91.11, https://stacks.math.columbia.edu/tag/0A4B.

import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Module.ZMod

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.subsingleton_etale_cohomology_restrict_injective_module_closed_fiber_prime
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (N : ℕ) (hN : N.Prime)
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ULift.{u} (ZMod N)))) (hJ : Injective J)
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (hG : G.obj = J.obj ⋙ forget₂ (ModuleCat.{u} (ULift.{u} (ZMod N))) AddCommGrpCat.{u})
    (q : ℕ) : Subsingleton (((PhilipponEtaleSmallSite.pullbackSheaves (pullback.snd (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) f)).obj G).H (q + 1)) := by sorry
