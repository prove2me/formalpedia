-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_traceDeterminantCongruences_mul_entries_mem
-- name    : Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences.mul_entries_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:25.351342+00:00
-- url     : https://prove2.me/theorems/70ff5fc0-288d-489f-8155-aed19e86075b
-- title:
--   trace Determinant Congruences: mul entries mem
-- statement:
--   The trace Determinant Congruences construction uses the mul entries mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensitySeventh.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensitySeventh.lean#L98-L101

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

theorem Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences.mul_entries_mem {r : Type} {J : Ideal (𝓞 K)} (M : Matrix m m (𝓞 K)) {R : Matrix m r (𝓞 K)}
    (hR : ∀ i j, R i j ∈ J) (i : m) (j : r) : (M * R) i j ∈ J := by sorry
