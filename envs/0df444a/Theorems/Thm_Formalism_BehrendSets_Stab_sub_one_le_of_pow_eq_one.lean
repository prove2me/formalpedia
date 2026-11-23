-- Prove2me | Theorems.Thm_Formalism_BehrendSets_Stab_sub_one_le_of_pow_eq_one
-- name    : Formalism.BehrendSets.Stab.sub_one_le_of_pow_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:00.921707+00:00
-- url     : https://prove2.me/theorems/62bd17c0-a391-4533-8d25-6fff3d90994c
-- title:
--   Stab: sub one le of pow eq one
-- statement:
--   The Stab construction uses the sub one le of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/TotientLeOfIsPrimitiveRoot.lean#L18-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/TotientLeOfIsPrimitiveRoot.lean#L18-L59

import Definitions.Def_Formalism_BehrendSets_StatementE
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_TotientLeOfIsPrimitiveRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Module Matrix
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Stab

theorem Formalism.BehrendSets.Stab.sub_one_le_of_pow_eq_one {E : Type} [Field E] [NumberField E] {k g : ℕ} (hg : g.Prime)
    (M : Matrix (Fin k) (Fin k) E) (hM : M ^ g = 1) (hM1 : M ≠ 1) :
    g - 1 ≤ finrank ℚ E * k := by sorry
