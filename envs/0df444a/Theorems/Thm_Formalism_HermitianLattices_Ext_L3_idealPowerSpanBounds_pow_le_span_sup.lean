-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_pow_le_span_sup
-- name    : Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.pow_le_span_sup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:14:38.438895+00:00
-- url     : https://prove2.me/theorems/5e29320f-b261-46d9-9222-297872791995
-- title:
--   ideal Power Span Bounds: pow le span sup
-- statement:
--   The ideal Power Span Bounds construction uses the pow le span sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtPPowLeSpanSup.lean#L15-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtPPowLeSpanSup.lean#L15-L28

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

theorem Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.pow_le_span_sup (hP : P.IsPrime) (hP0 : P ≠ ⊥) {g : R} {c : ℕ} (hg : g ∉ P ^ (c + 1)) (N : ℕ) :
    P ^ c ≤ Ideal.span {g} ⊔ P ^ N := by sorry
