-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lsat_eval_colAddGen
-- name    : Formalism.GradedWeylDivisibility.lsat_eval_colAddGen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:37.524845+00:00
-- url     : https://prove2.me/theorems/eb9c837a-1209-43af-9b99-c26d3cdd5a40
-- title:
--   Graded Weyl Divisibility: lsat eval col Add Gen
-- statement:
--   The Graded Weyl Divisibility construction uses the lsat eval col Add Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylPoint.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylPoint.lean#L24-L30

import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LSatLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylPoint
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

theorem Formalism.GradedWeylDivisibility.lsat_eval_colAddGen {R : Type*} [CommRing R] {r n : ℕ} (l j : Fin n)
    (x : Option (Fin r × Fin n) → R) :
    (aeval x).comp (colAddGen R l j) = (aeval (x ∘ some)).comp (colAdd R l j (x none)) := by sorry
