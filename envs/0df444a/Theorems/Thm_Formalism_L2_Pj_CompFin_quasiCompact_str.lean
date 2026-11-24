-- Prove2me | Theorems.Thm_Formalism_L2_Pj_CompFin_quasiCompact_str
-- name    : Formalism.L2.Pj.CompFin.quasiCompact_str
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:01.765336+00:00
-- url     : https://prove2.me/theorems/523eef15-04b6-4a40-b56e-e4071217bc3d
-- title:
--   Comp Fin: quasi Compact str
-- statement:
--   The Comp Fin construction uses the quasi Compact str property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompFin.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompFin.lean#L24-L27

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

theorem Formalism.L2.Pj.CompFin.quasiCompact_str (R : Type) [CommRing R] (N : ℕ) : QuasiCompact (PSpace.str R N) := by sorry
