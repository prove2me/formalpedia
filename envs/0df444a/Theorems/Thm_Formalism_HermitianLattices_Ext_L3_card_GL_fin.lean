-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_card_GL_fin
-- name    : Formalism.HermitianLattices.Ext.L3.card_GL_fin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:00.954807+00:00
-- url     : https://prove2.me/theorems/ac9e62e9-8f3b-487e-a5e7-6ea6aab8874e
-- title:
--   L3: card GL fin
-- statement:
--   The L3 construction uses the card GL fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryFin.lean#L279-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryFin.lean#L279-L302

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryFin
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

theorem Formalism.HermitianLattices.Ext.L3.card_GL_fin {k : Type*} [Field k] [Fintype k] (q : ℕ) (hq : Fintype.card k = q) (m : ℕ) :
    (Nat.card (GL (Fin m) k) : ℝ) = (q : ℝ) ^ (m ^ 2) * ∏ j ∈ Finset.Icc 1 m, (1 - (q : ℝ)⁻¹ ^ j) := by sorry
