-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_rename_rowAct
-- name    : Formalism.GradedWeylDivisibility.rename_rowAct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:11.48481+00:00
-- url     : https://prove2.me/theorems/fcc83983-850e-4559-bb14-88abe3ec9c9a
-- title:
--   Graded Weyl Divisibility: rename row Act
-- statement:
--   The Graded Weyl Divisibility construction uses the rename row Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LRowstLemmas.lean#L102-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LRowstLemmas.lean#L102-L111

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

theorem Formalism.GradedWeylDivisibility.rename_rowAct {R : Type*} [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (f : MvPolynomial (Fin r × Fin n) R) :
    rename (some : Fin r × Fin n → Option (Fin r × Fin n)) (rowAct R g f) =
      rowActO R g (rename some f) := by sorry
