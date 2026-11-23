-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_conj_col
-- name    : Formalism.QuantumDeterminants.WeylGroupFacts.conj_col
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:02.762714+00:00
-- url     : https://prove2.me/theorems/4e30d9e3-8c5f-42c3-a44a-0de5e0ca83ff
-- title:
--   Weyl Group Facts: conj col
-- statement:
--   The Weyl Group Facts construction uses the conj col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/UnitaryWeylNormalHolds.lean#L377-L394
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/UnitaryWeylNormalHolds.lean#L377-L394

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}

theorem Formalism.QuantumDeterminants.WeylGroupFacts.conj_col {h h' g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : block k r h) (hh' : block k r h') (hinv : h * h' = 1) (hg : col k r g) :
    col k r (h * g * h') := by sorry
