-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_isotropic_to_std_subst_harmonic
-- name    : Formalism.L2.FormalSeriesBounds.RF.isotropic_to_std_subst_harmonic
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-27T05:44:58.734131+00:00
-- url     : https://prove2.me/theorems/a25e1a94-6dc2-5d3c-818b-5c2ff4af741a
-- title:
--   RF: isotropic to std subst harmonic
-- statement:
--   The RF construction uses the isotropic to std subst harmonic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieMemCHarm.lean#L166-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieMemCHarm.lean#L166-L192

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PderivSubGOff
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCHarm
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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

theorem Formalism.L2.FormalSeriesBounds.RF.isotropic_to_std_subst_harmonic : IsotropicToStdSubstHarmonic := by sorry
