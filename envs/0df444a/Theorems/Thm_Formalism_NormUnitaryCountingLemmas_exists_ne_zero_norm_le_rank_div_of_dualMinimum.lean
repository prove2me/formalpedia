-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_exists_ne_zero_norm_le_rank_div_of_dualMinimum
-- name    : Formalism.NormUnitaryCountingLemmas.exists_ne_zero_norm_le_rank_div_of_dualMinimum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:54.272449+00:00
-- url     : https://prove2.me/theorems/9d0ef9c3-3915-4bc2-aa2c-e5bb948c475d
-- title:
--   Norm Unitary Counting Lemmas: exists ne zero norm le rank div of dual Minimum
-- statement:
--   The Norm Unitary Counting Lemmas construction uses the exists ne zero norm le rank div of dual Minimum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ExistsNeZeroNormLeRankDivOfDualMinimum.lean#L35-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ExistsNeZeroNormLeRankDivOfDualMinimum.lean#L35-L151

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolPos
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqCovolume
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_ShortVector
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ExistsNeZeroNormLeRankDivOfDualMinimum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem Formalism.NormUnitaryCountingLemmas.exists_ne_zero_norm_le_rank_div_of_dualMinimum (Q : Submodule ℤ E) [hQd : DiscreteTopology Q] (hQ : Q ≠ ⊥) {l : ℝ}
    (hl : 0 < l)
    (hdual : ∀ y ∈ span ℝ (Q : Set E), y ≠ 0 →
      (∀ x ∈ Q, ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → l ≤ ‖y‖) :
    ∃ q ∈ Q, q ≠ 0 ∧ ‖q‖ ≤ (Formalism.F.rk Q : ℝ) / l := by sorry
