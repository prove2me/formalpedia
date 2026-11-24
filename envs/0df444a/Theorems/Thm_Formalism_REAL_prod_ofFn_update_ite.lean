-- Prove2me | Theorems.Thm_Formalism_REAL_prod_ofFn_update_ite
-- name    : Formalism.REAL.prod_ofFn_update_ite
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:24:12.904524+00:00
-- url     : https://prove2.me/theorems/f339189d-fb42-4fe8-8f2a-c30e2c298a7f
-- title:
--   REAL: prod of Fn update ite
-- statement:
--   The REAL construction uses the prod of Fn update ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/GeneratorCommutatorQuantumDet.lean#L58-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/GeneratorCommutatorQuantumDet.lean#L58-L66

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

theorem Formalism.REAL.prod_ofFn_update_ite {A : Type*} [Ring A] {t : ℕ} (F : Fin t → A) (k : Fin t) (p : Prop)
    [Decidable p] (x : A) :
    (List.ofFn (Function.update F k (if p then x else 0))).prod =
      if p then (List.ofFn (Function.update F k x)).prod else 0 := by sorry
