-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_gram_det_change
-- name    : Formalism.HermitianLattices.Ext.L3.gram_det_change
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:02.174328+00:00
-- url     : https://prove2.me/theorems/f5f9ddf9-95d2-4953-b9a4-68324bc9e879
-- title:
--   L3: gram det change
-- statement:
--   The L3 construction uses the gram det change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/GramEqConjTransposeMul.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/GramEqConjTransposeMul.lean#L22-L27

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandG
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GramEqConjTransposeMul
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3

theorem Formalism.HermitianLattices.Ext.L3.gram_det_change {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {n : ℕ}
    (h : V →ₗ⋆[K] V →ₗ[K] K) (b b' : Basis (Fin n) K V) :
    (gram h b).det = star (b'.det b) * b'.det b * (gram h b').det := by sorry
