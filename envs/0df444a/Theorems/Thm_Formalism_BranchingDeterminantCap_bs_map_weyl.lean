-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bs_map_weyl
-- name    : Formalism.BranchingDeterminantCap.bs_map_weyl
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:23:38.4578+00:00
-- url     : https://prove2.me/theorems/e08d9569-71a3-431b-9d2a-79e928f7ab9a
-- title:
--   Branching Determinant Cap: bs map weyl
-- statement:
--   The Branching Determinant Cap construction uses the bs map weyl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L39-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L39-L51

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

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

theorem Formalism.BranchingDeterminantCap.bs_map_weyl {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) ℚ)
    (hf : f ∈ weyl ℚ r n hn ν) : map (algebraMap ℚ ℂ) f ∈ weyl ℂ r n hn ν := by sorry
