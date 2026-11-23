-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mul_notMem
-- name    : Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.mul_notMem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:55:30.878351+00:00
-- url     : https://prove2.me/theorems/09aa68ea-c7df-4b5d-88a4-cee9190af2b8
-- title:
--   ideal Power Span Bounds: mul not Mem
-- statement:
--   The ideal Power Span Bounds construction uses the mul not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtPPowLeSpanSup.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtPPowLeSpanSup.lean#L60-L67

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {P : Ideal R}

theorem Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.mul_notMem (hP : P.IsPrime) (hP0 : P ≠ ⊥) {a b : R} {i j : ℕ} (ha : a ∉ P ^ (i + 1))
    (hb : b ∉ P ^ (j + 1)) : a * b ∉ P ^ (i + j + 1) := by sorry
