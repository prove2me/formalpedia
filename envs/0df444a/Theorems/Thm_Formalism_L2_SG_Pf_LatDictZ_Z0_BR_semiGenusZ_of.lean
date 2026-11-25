-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_semiGenusZ_of
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z0.BR.semiGenusZ_of
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:56:27.773263+00:00
-- url     : https://prove2.me/theorems/d9e5a0a4-7a72-4852-97a5-136cc815f7c4
-- title:
--   BR: semi Genus Z of
-- statement:
--   The BR construction uses the semi Genus Z of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/AlgebraMapNeZero.lean#L41-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/AlgebraMapNeZero.lean#L41-L88

import Mathlib
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_UnimodOfSelfDual
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_AlgebraMapNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.BR
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA PIW.AdelClassFin
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem Formalism.L2.SG.Pf.LatDictZ.Z0.BR.semiGenusZ_of (hZ : SemiGenusZLoc) : SemiGenusZ := by sorry
