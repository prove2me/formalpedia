-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_card_prod_set
-- name    : Formalism.FourierDecayAlt.P.S3x3.card_prod_set
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:20.568043+00:00
-- url     : https://prove2.me/theorems/3120f37c-6cd8-4907-8a48-fd9f245366c7
-- title:
--   S3x3: card prod set
-- statement:
--   The S3x3 construction uses the card prod set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L460-L479
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean#L460-L479

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x3
open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni upUniG)
variable {A : Type} [CommRing A] {r k : ℕ}

theorem Formalism.FourierDecayAlt.P.S3x3.card_prod_set (Q : Matrix (Fin k) (Fin k) A → Prop) (hQ : ∀ h, Q h → IsUnit h.det) :
    Nat.card {x : Matrix (Idx r k) (Idx r k) A //
        ∃ n h', IsN n ∧ (∃ h, Q h ∧ h' = hEmb r h) ∧ x = n * h'} =
      Nat.card {g : GL (Fin k) A // Q g} * Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsN x} := by sorry
