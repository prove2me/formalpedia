-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_smul_eq_alg
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z0.BR.smul_eq_alg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:59:27.935667+00:00
-- url     : https://prove2.me/theorems/6ef05ff8-ac2e-4702-80b8-91522041c3c0
-- title:
--   BR: smul eq alg
-- statement:
--   The BR construction uses the smul eq alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/AlgebraMapNeZero.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/AlgebraMapNeZero.lean#L38-L39

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

theorem Formalism.L2.SG.Pf.LatDictZ.Z0.BR.smul_eq_alg (t : 𝓞 E) (v : Fin n → E) : t • v = (algebraMap (𝓞 E) E t) • v := by sorry
