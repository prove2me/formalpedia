-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_summable_sq_geom
-- name    : Formalism.HermitianLattices.Ext.L3.A5.summable_sq_geom
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:11.202722+00:00
-- url     : https://prove2.me/theorems/975c3d1f-5747-45b0-af99-4500df637cfd
-- title:
--   A5: summable sq geom
-- statement:
--   The A5 construction uses the summable sq geom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SummableSqGeom.lean#L93-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SummableSqGeom.lean#L93-L101

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.A5
variable {ι : Type*}

theorem Formalism.HermitianLattices.Ext.L3.A5.summable_sq_geom : Summable fun j : ℕ => 8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j := by sorry
