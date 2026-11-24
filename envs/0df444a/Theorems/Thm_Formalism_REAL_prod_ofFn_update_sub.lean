-- Prove2me | Theorems.Thm_Formalism_REAL_prod_ofFn_update_sub
-- name    : Formalism.REAL.prod_ofFn_update_sub
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:24:09.895831+00:00
-- url     : https://prove2.me/theorems/14dcead5-ff9c-48aa-b4c4-0a1b8b254619
-- title:
--   REAL: prod of Fn update sub
-- statement:
--   The REAL construction uses the prod of Fn update sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/GeneratorCommutatorQuantumDet.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/GeneratorCommutatorQuantumDet.lean#L52-L56

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL

theorem Formalism.REAL.prod_ofFn_update_sub {A : Type*} [Ring A] {t : ℕ} (F : Fin t → A) (k : Fin t) (x y : A) :
    (List.ofFn (Function.update F k (x - y))).prod =
      (List.ofFn (Function.update F k x)).prod - (List.ofFn (Function.update F k y)).prod := by sorry
