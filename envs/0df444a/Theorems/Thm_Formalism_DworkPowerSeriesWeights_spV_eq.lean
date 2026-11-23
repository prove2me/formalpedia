-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_spV_eq
-- name    : Formalism.DworkPowerSeriesWeights.spV_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:00.199897+00:00
-- url     : https://prove2.me/theorems/e5b7771a-5791-4a7a-aecb-3504cefad15e
-- title:
--   Dwork Power Series Weights: sp V eq
-- statement:
--   The Dwork Power Series Weights construction uses the sp V eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L338-L343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L338-L343

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {R : Type*} [CommRing R] {m p : ℕ}

theorem Formalism.DworkPowerSeriesWeights.spV_eq (top : Fin (p + 1) → R) (o : Option (Fin m)) (c : Fin (p + 1)) :
    spV top o c = MvPolynomial.monomial (spEx o c) (spCo top o c) := by sorry
