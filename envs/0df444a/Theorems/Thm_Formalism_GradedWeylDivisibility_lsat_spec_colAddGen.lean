-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lsat_spec_colAddGen
-- name    : Formalism.GradedWeylDivisibility.lsat_spec_colAddGen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:04:28.777936+00:00
-- url     : https://prove2.me/theorems/80bc052c-b397-4fff-bf18-7dc5b26e42fb
-- title:
--   Graded Weyl Divisibility: lsat spec col Add Gen
-- statement:
--   The Graded Weyl Divisibility construction uses the lsat spec col Add Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylPoint.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylPoint.lean#L9-L15

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

theorem Formalism.GradedWeylDivisibility.lsat_spec_colAddGen {R : Type*} [CommRing R] {r n : ℕ} (l j : Fin n) (c : R) :
    (aeval (fun o : Option (Fin r × Fin n) => Option.elim o (C c) X)).comp (colAddGen R l j) =
      colAdd R l j c := by sorry
