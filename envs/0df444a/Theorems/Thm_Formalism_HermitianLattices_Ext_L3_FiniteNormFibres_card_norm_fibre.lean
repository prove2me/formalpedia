-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteNormFibres_card_norm_fibre
-- name    : Formalism.HermitianLattices.Ext.L3.FiniteNormFibres.card_norm_fibre
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:04.0871+00:00
-- url     : https://prove2.me/theorems/d2f96106-36d7-4bd3-92d2-d4caa31946c0
-- title:
--   Finite Norm Fibres: card norm fibre
-- statement:
--   The Finite Norm Fibres construction uses the card norm fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardSumNormFibres.lean#L113-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardSumNormFibres.lean#L113-L205

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

theorem Formalism.HermitianLattices.Ext.L3.FiniteNormFibres.card_norm_fibre {k : Type*} [Field k] [Fintype k] [DecidableEq k] (σ : k ≃+* k)
    (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) (q : ℕ) (hq : Fintype.card k = q ^ 2)
    (c : k) (hc : σ c = c) :
    ((univ.filter (fun y : k => σ y * y = c)).card : ℤ) =
      ((q : ℤ) - (-1)) + (-1) * (q : ℤ) * (if c = 0 then 1 else 0) := by sorry
