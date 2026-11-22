-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_subsingleton_etale_cohomology_restrict_injective_module_closed_fiber
-- name    : AlgebraicGeometry.Scheme.subsingleton_etale_cohomology_restrict_injective_module_closed_fiber
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-21T18:40:34.010379+00:00
-- url     : https://prove2.me/theorems/e9ff6a3e-cde9-4529-bc8c-b72061025245
-- title:
--   The closed-fiber restriction of an injective étale module sheaf is acyclic
-- statement:
--   Let $Y$ be proper over a strictly henselian local ring, with closed fiber inclusion $i$. Let $J$ be an injective sheaf of $mathbf Z/Nmathbf Z$-modules on the small étale site of $Y$, where $N>0$, and $G$ its underlying abelian sheaf. Then $H^m(Y_0,i^*G)=0$ for all $m>0$.
-- source:
--   Consequence of Stacks Project, Theorem 59.91.11, https://stacks.math.columbia.edu/tag/095T.

import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Module.ZMod

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.subsingleton_etale_cohomology_restrict_injective_module_closed_fiber
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (N : ℕ) (hN : N ≠ 0)
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ULift.{u} (ZMod N)))) (hJ : Injective J)
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (hG : G.obj = J.obj ⋙ forget₂ (ModuleCat.{u} (ULift.{u} (ZMod N))) AddCommGrpCat.{u})
    (q : ℕ) : Subsingleton (((PhilipponEtaleSmallSite.pullbackSheaves (pullback.snd (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) f)).obj G).H (q + 1)) := by sorry
