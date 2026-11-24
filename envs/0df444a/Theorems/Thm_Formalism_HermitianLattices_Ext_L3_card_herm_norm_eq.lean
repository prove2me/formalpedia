-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_card_herm_norm_eq
-- name    : Formalism.HermitianLattices.Ext.L3.card_herm_norm_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:15:09.181491+00:00
-- url     : https://prove2.me/theorems/3cc27cb4-9b23-4d71-9232-0d156e94932e
-- title:
--   L3: card herm norm eq
-- statement:
--   The L3 construction uses the card herm norm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardSumNormFibres.lean#L243-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardSumNormFibres.lean#L243-L267

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

theorem Formalism.HermitianLattices.Ext.L3.card_herm_norm_eq {k : Type*} [Field k] [Fintype k] (σ : k ≃+* k)
    (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) (q : ℕ) (hq : Fintype.card k = q ^ 2)
    (M : ℕ) (hM : 1 ≤ M) (c : k) (hc : σ c = c) (hc0 : c ≠ 0) :
    (Nat.card {x : Fin M → k // ∑ i, σ (x i) * x i = c} : ℤ) =
      (q : ℤ) ^ (M - 1) * ((q : ℤ) ^ M - (-1) ^ M) := by sorry
