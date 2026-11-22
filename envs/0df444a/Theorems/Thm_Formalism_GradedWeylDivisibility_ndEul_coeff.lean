-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ndEul_coeff
-- name    : Formalism.GradedWeylDivisibility.ndEul_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:09:15.360802+00:00
-- url     : https://prove2.me/theorems/d9a93359-8f8f-4d7c-9730-296fcc7104d3
-- title:
--   Graded Weyl Divisibility: nd Eul coeff
-- statement:
--   The Graded Weyl Divisibility construction uses the nd Eul coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LNondomLemmas.lean#L31-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LNondomLemmas.lean#L31-L56

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas
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
set_option linter.unusedSimpArgs false
variable {R : Type*} [CommRing R] {r n : ℕ}

theorem Formalism.GradedWeylDivisibility.ndEul_coeff (s : Fin n) (g : MvPolynomial (Fin r × Fin n) R) (m : Fin r × Fin n →₀ ℕ) :
    coeff m (ndEul R r n s g) =
      (Finsupp.weight (fun v => colW r n v s) m : R) * coeff m g := by sorry
