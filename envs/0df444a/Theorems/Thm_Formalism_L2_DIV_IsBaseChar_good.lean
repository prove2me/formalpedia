-- Prove2me | Theorems.Thm_Formalism_L2_DIV_IsBaseChar_good
-- name    : Formalism.L2.DIV.IsBaseChar.good
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:26:03.706725+00:00
-- url     : https://prove2.me/theorems/9dee19bf-8372-4b8b-b353-651fa5cce729
-- title:
--   Is Base Char: good
-- statement:
--   The Is Base Char construction uses the good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/TuplesLemmas.lean#L49-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/TuplesLemmas.lean#L49-L59

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Tuples
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism Formalism.L2 Formalism.L2.DIV

theorem Formalism.L2.DIV.IsBaseChar.good {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type}
    [Field L] {S : Set ℕ} {p : ℕ} (δ : Tup F E L S) (h : IsBaseChar p (δ : Chr F E L))
    (v : HeightOneSpectrum (𝓞 F)) (hv : plc v = p) : GoodPl E S v := by sorry
