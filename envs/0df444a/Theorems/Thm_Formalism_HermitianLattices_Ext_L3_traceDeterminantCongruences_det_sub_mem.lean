-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_traceDeterminantCongruences_det_sub_mem
-- name    : Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences.det_sub_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:46:25.215814+00:00
-- url     : https://prove2.me/theorems/840feb8e-5965-528f-8881-3c2d4d3c16d4
-- title:
--   trace Determinant Congruences: det sub mem
-- statement:
--   The trace Determinant Congruences construction uses the det sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensitySeventh.lean#L103-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensitySeventh.lean#L103-L110

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySeventh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
open idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable {m : Type} [Fintype m] [DecidableEq m]

theorem Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences.det_sub_mem {J : Ideal (𝓞 K)} {M N : Matrix m m (𝓞 K)} (h : ∀ i j, (M - N) i j ∈ J) :
    M.det - N.det ∈ J := by sorry
