-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_colAddGen_rowAct
-- name    : Formalism.GradedWeylDivisibility.colAddGen_rowAct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:50.338367+00:00
-- url     : https://prove2.me/theorems/07e05fff-38ce-4325-a8fa-63b79c52db6c
-- title:
--   Graded Weyl Divisibility: col Add Gen row Act
-- statement:
--   The Graded Weyl Divisibility construction uses the col Add Gen row Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LRowstLemmas.lean#L86-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LRowstLemmas.lean#L86-L100

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

theorem Formalism.GradedWeylDivisibility.colAddGen_rowAct {R : Type*} [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (l j : Fin n) (f : MvPolynomial (Fin r × Fin n) R) :
    colAddGen R l j (rowAct R g f) = rowActO R g (colAddGen R l j f) := by sorry
