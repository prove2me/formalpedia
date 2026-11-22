-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_smul
-- name    : Formalism.HermitianLattices.Ext.L3.HU.Ent.smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:29:58.23081+00:00
-- url     : https://prove2.me/theorems/e50d3737-5f4a-44f8-98f7-551e64f838b1
-- title:
--   Ent: smul
-- statement:
--   The Ent construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsLocUnif.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsLocUnif.lean#L36-L37

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

theorem Formalism.HermitianLattices.Ext.L3.HU.Ent.smul {a : K} (ha : a ∈ S) {M : Matrix m n K} (hM : Ent S M) : Ent S (a • M) := by sorry
