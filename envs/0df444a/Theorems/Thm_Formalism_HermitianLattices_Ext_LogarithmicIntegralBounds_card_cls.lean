-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_card_cls
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.card_cls
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:40:53.764749+00:00
-- url     : https://prove2.me/theorems/1513ccbd-2118-441a-96f4-ebb519314fd3
-- title:
--   Logarithmic Integral Bounds: card cls
-- statement:
--   The Logarithmic Integral Bounds construction uses the card cls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqOrth.lean#L142-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqOrth.lean#L142-L174

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqOrth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.card_cls (m₀ s a : ℕ) (hcop : m₀.Coprime s) (hm : m₀ ≠ 0) (hs : s ≠ 0) :
    ((range (m₀ * s)).filter (fun b => b % m₀ = a % m₀ ∧ b.Coprime s)).card = s.totient := by sorry
