-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_rowAct_X_isWH
-- name    : Formalism.GradedWeylDivisibility.rowAct_X_isWH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:16.467933+00:00
-- url     : https://prove2.me/theorems/5798ddb0-8098-4efd-991c-49da1b64561e
-- title:
--   Graded Weyl Divisibility: row Act X is WH
-- statement:
--   The Graded Weyl Divisibility construction uses the row Act X is WH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LRowstLemmas.lean#L113-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LRowstLemmas.lean#L113-L119

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowstLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.rowAct_X_isWH {R : Type*} [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (v : Fin r × Fin n) : IsWeightedHomogeneous (colW r n) (rowAct R g (X v)) (colW r n v) := by sorry
