-- Prove2me | Theorems.Thm_AlgebraicGeometry_smooth_of_regular_stalks_over_perfect_field
-- name    : AlgebraicGeometry.smooth_of_regular_stalks_over_perfect_field
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-28T18:15:26.45598+00:00
-- url     : https://prove2.me/theorems/7969cf08-06cd-40d3-81b4-8adffe115fe3
-- title:
--   Regular schemes locally of finite type over a perfect field are smooth
-- statement:
--   Let $K$ be a perfect field, and let $Y$ be a scheme with a structure morphism $\pi:Y\to\operatorname{Spec}K$ locally of finite type. If every local ring of $Y$ is regular, then
--   $$\pi:Y\longrightarrow\operatorname{Spec}K\quad\text{is smooth}.$$
--   The scheme need not be affine, proper, connected or integral, and the empty scheme is allowed. Perfectness is essential: regularity over an imperfect field alone does not imply smoothness.
--
--   This criterion converts an alteration with regular local rings into a smooth cover over a perfect ground field.
-- source:
--   The Stacks Project, Lemma 33.12.3, Tag 038V, https://stacks.math.columbia.edu/tag/038V , and Lemma 33.12.6, Tag 038X, https://stacks.math.columbia.edu/tag/038X . The first tests geometric regularity on finite purely inseparable field extensions; over a perfect field these extensions are trivial. The second identifies geometric regularity with smoothness for schemes locally of finite type over a field. This is their combined scheme-level consequence; pointwise regularity is the actual IsRegularLocalRing predicate, not an assumed smoothness certificate.

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.RegularLocalRing.Defs
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u

theorem AlgebraicGeometry.smooth_of_regular_stalks_over_perfect_field
    (K : Type u) [Field K] [PerfectField K] {Y : Scheme.{u}}
    (π : Y ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) :
    Smooth π := by sorry
