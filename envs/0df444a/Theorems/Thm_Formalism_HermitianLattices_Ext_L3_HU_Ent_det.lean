-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_det
-- name    : Formalism.HermitianLattices.Ext.L3.HU.Ent.det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:29:46.827528+00:00
-- url     : https://prove2.me/theorems/5f335d73-7547-422f-b9ba-ea928c58da39
-- title:
--   Ent: det
-- statement:
--   The Ent construction uses the det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsLocUnif.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsLocUnif.lean#L61-L66

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
variable {K : Type*} [Field K] [StarRing K]
variable {S : Subring K} {m n o : Type*}

theorem Formalism.HermitianLattices.Ext.L3.HU.Ent.det [Fintype n] [DecidableEq n] {M : Matrix n n K} (hM : Ent S M) : M.det ∈ S := by sorry
