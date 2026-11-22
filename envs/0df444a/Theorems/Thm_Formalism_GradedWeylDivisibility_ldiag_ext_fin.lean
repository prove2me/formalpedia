-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldiag_ext_fin
-- name    : Formalism.GradedWeylDivisibility.ldiag_ext_fin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:22:34.769262+00:00
-- url     : https://prove2.me/theorems/ba8de152-b525-425c-bcbe-3431072aaf11
-- title:
--   Graded Weyl Divisibility: ldiag ext fin
-- statement:
--   The Graded Weyl Divisibility construction uses the ldiag ext fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DomPow.lean#L63-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DomPow.lean#L63-L64

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DomPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.ldiag_ext_fin {α : Type*} [Zero α] {r : ℕ} (f : Fin r → α) (a : Fin r) : ldiagExt f a = f a := by sorry
