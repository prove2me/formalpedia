-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeyl_mul
-- name    : Formalism.GradedWeylDivisibility.dualWeyl_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:59:55.336953+00:00
-- url     : https://prove2.me/theorems/6f298b64-d16d-47b9-ad46-bd10e5b72730
-- title:
--   Graded Weyl Divisibility: dual Weyl mul
-- statement:
--   The Graded Weyl Divisibility construction uses the dual Weyl mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetLemmas.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetLemmas.lean#L18-L24

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
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

theorem Formalism.GradedWeylDivisibility.dualWeyl_mul {R : Type*} [CommRing R] {r n : ℕ} {ν μ : Fin n → ℕ}
    {f g : MvPolynomial (Fin r × Fin n) R}
    (hf : f ∈ dualWeyl R r n ν) (hg : g ∈ dualWeyl R r n μ) :
    f * g ∈ dualWeyl R r n (ν + μ) := by sorry
