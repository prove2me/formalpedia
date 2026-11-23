-- Prove2me | Theorems.Thm_Formalism_L2_Pj_CompFin_finiteType_zero
-- name    : Formalism.L2.Pj.CompFin.finiteType_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:41:43.217545+00:00
-- url     : https://prove2.me/theorems/b8c227f5-bfd2-4d99-8948-912473088b9b
-- title:
--   Comp Fin: finite Type zero
-- statement:
--   The Comp Fin construction uses the finite Type zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompFin.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompFin.lean#L11-L22

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.CompFin
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem Formalism.L2.Pj.CompFin.finiteType_zero (R : Type) [CommRing R] (N : ℕ) :
    Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) (MvPolynomial (Fin (N + 1)) R) := by sorry
