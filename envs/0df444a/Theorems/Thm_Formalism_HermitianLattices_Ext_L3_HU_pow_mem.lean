-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_pow_mem
-- name    : Formalism.HermitianLattices.Ext.L3.HU.pow_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:29:49.436049+00:00
-- url     : https://prove2.me/theorems/b53540f3-9727-4cbe-a9c5-a51fea14bfb6
-- title:
--   HU: pow mem
-- statement:
--   The HU construction uses the pow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsLocUnif.lean#L77-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsLocUnif.lean#L77-L78

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

theorem Formalism.HermitianLattices.Ext.L3.HU.pow_mem {ϖ : K} (hS : IsLocUnif S ϖ) (k : ℕ) : ϖ ^ k ∈ S := by sorry
