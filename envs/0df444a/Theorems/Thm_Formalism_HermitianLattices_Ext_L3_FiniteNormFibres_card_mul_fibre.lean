-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteNormFibres_card_mul_fibre
-- name    : Formalism.HermitianLattices.Ext.L3.FiniteNormFibres.card_mul_fibre
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:45:21.708422+00:00
-- url     : https://prove2.me/theorems/b3f93b19-6e33-48ea-a13d-12dd0a1edd67
-- title:
--   Finite Norm Fibres: card mul fibre
-- statement:
--   The Finite Norm Fibres construction uses the card mul fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardSumNormFibres.lean#L207-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardSumNormFibres.lean#L207-L237

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.FiniteNormFibres

theorem Formalism.HermitianLattices.Ext.L3.FiniteNormFibres.card_mul_fibre {k : Type*} [Field k] [Fintype k] [DecidableEq k] (c : k) :
    ((univ.filter (fun y : k × k => y.1 * y.2 = c)).card : ℤ) =
      ((Fintype.card k : ℤ) - 1) + 1 * (Fintype.card k : ℤ) * (if c = 0 then 1 else 0) := by sorry
