-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bs_hwspace
-- name    : Formalism.BranchingDeterminantCap.bs_hwspace
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:26:17.010101+00:00
-- url     : https://prove2.me/theorems/a734c020-2192-4379-ae72-583aef412033
-- title:
--   Branching Determinant Cap: bs hwspace
-- statement:
--   The Branching Determinant Cap construction uses the bs hwspace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L127-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L127-L148

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
open Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap

theorem Formalism.BranchingDeterminantCap.bs_hwspace {n : ℕ} (sg : Fin n → ℕ) (hsg : Antitone sg) (q : MvPolynomial (Fin n × Fin n) ℂ)
    (hq : q ∈ dualWeyl ℂ n n sg) (hqw : IsWeightedHomogeneous (rowW n n) q sg) :
    ∃ c : ℂ, q = c • hw ℂ le_rfl sg := by sorry
