-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_card_dot_eq
-- name    : Formalism.HermitianLattices.Ext.L3.card_dot_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:52.831164+00:00
-- url     : https://prove2.me/theorems/86b015eb-3c81-47af-9fcd-7d09d6710151
-- title:
--   L3: card dot eq
-- statement:
--   The L3 construction uses the card dot eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardSumNormFibres.lean#L269-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardSumNormFibres.lean#L269-L295

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3

theorem Formalism.HermitianLattices.Ext.L3.card_dot_eq {k : Type*} [Field k] [Fintype k] (q : ℕ) (hq : Fintype.card k = q)
    (M : ℕ) (hM : 1 ≤ M) (c : k) (hc : c ≠ 0) :
    (Nat.card {x : (Fin M → k) × (Fin M → k) // ∑ i, x.1 i * x.2 i = c} : ℤ) =
      (q : ℤ) ^ (2 * M - 1) - (q : ℤ) ^ (M - 1) := by sorry
