-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_rowPart_single
-- name    : Formalism.GradedWeylDivisibility.rowPart_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:19.832804+00:00
-- url     : https://prove2.me/theorems/dee65ee6-d082-456f-a972-193542f5c4e2
-- title:
--   Graded Weyl Divisibility: row Part single
-- statement:
--   The Graded Weyl Divisibility construction uses the row Part single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetdomLemmas.lean#L74-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetdomLemmas.lean#L74-L80

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetdomLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.rowPart_single {r n : ℕ} (k : ℕ) (b : Fin r) (s : Fin n) :
    rowPart k (Finsupp.single (b, s) 1 : Fin r × Fin n →₀ ℕ) = if b.val < k then 1 else 0 := by sorry
