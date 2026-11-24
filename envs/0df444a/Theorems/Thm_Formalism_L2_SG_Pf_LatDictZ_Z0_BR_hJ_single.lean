-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_hJ_single
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z0.BR.hJ_single
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:37:01.119399+00:00
-- url     : https://prove2.me/theorems/e8d26f00-9b6b-41bc-ad0d-0143ca8cda08
-- title:
--   BR: h J single
-- statement:
--   The BR construction uses the h J single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/UnimodOfSelfDual.lean#L48-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/UnimodOfSelfDual.lean#L48-L55

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_UnimodOfSelfDual
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

theorem Formalism.L2.SG.Pf.LatDictZ.Z0.BR.hJ_single (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (j : Fin n) :
    hJ J x (Pi.single j 1) = (Matrix.vecMul (fun i => starRingEnd E (x i)) J) j := by sorry
