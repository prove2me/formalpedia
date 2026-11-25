-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_subsingleton_etale_cohomology_constant_closed_of_isAlgClosed_fractionRing
-- name    : AlgebraicGeometry.Scheme.subsingleton_etale_cohomology_constant_closed_of_isAlgClosed_fractionRing
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-25T00:59:56.508608+00:00
-- url     : https://prove2.me/theorems/4a28918f-d6eb-4a41-99a5-82545295d7ee
-- title:
--   Constant étale cohomology vanishes on closed subschemes of an absolutely integrally closed domain
-- statement:
--   Let $R$ be an integrally closed domain with algebraically
--       closed fraction field and $T$ a closed subscheme of $\operatorname{Spec}R$.
--       Then $H^{q+1}_{\acute{e}tale}(T,\underline M)=0$ for every finite abelian group $M$.
-- source:
--   Stacks Project, Lemma 59.80.8, https://stacks.math.columbia.edu/tag/09ZC.

import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts
import Mathlib.RingTheory.Henselian

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtaleSmallSite (pullbackSheaves)
universe u
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackAdjunction)

theorem AlgebraicGeometry.Scheme.subsingleton_etale_cohomology_constant_closed_of_isAlgClosed_fractionRing
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsAlgClosed (FractionRing R)]
    {T : Scheme.{u}} (e : T ⟶ Spec (.of R)) [IsClosedImmersion e]
    (M : AddCommGrpCat.{u}) (_ : Finite M) (q : ℕ) :
    Subsingleton (((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u}).obj M).H (q + 1)) := by sorry
