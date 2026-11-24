-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lctwo_sum_ite
-- name    : Formalism.GradedWeylDivisibility.lctwo_sum_ite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:37.667935+00:00
-- url     : https://prove2.me/theorems/73b00bcb-2b1b-4149-a8d5-ca4eda412614
-- title:
--   Graded Weyl Divisibility: lctwo sum ite
-- statement:
--   The Graded Weyl Divisibility construction uses the lctwo sum ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TwoColumn.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TwoColumn.lean#L41-L45

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_TwoColumn
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

theorem Formalism.GradedWeylDivisibility.lctwo_sum_ite {r : ℕ} (a : Fin r) (e : ℕ) (f : Fin r → ℕ) (P : Fin r → Prop) [DecidablePred P] :
    (∑ b : Fin r with P b, ((if a = b then e else 0) + f b)) =
      (if P a then e else 0) + ∑ b : Fin r with P b, f b := by sorry
