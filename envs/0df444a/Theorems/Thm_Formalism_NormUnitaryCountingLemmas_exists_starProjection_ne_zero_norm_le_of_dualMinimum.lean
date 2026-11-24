-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_exists_starProjection_ne_zero_norm_le_of_dualMinimum
-- name    : Formalism.NormUnitaryCountingLemmas.exists_starProjection_ne_zero_norm_le_of_dualMinimum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:18:29.069824+00:00
-- url     : https://prove2.me/theorems/78c8599c-bc02-40c1-a46a-56e34a721315
-- title:
--   Norm Unitary Counting Lemmas: exists star Projection ne zero norm le of dual Minimum
-- statement:
--   The Norm Unitary Counting Lemmas construction uses the exists star Projection ne zero norm le of dual Minimum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShortIndependentVectorsOfDualMinimum.lean#L16-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShortIndependentVectorsOfDualMinimum.lean#L16-L79

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ExistsNeZeroNormLeRankDivOfDualMinimum
import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SaturationProperties
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DegQuot
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShortIndependentVectorsOfDualMinimum
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

theorem Formalism.NormUnitaryCountingLemmas.exists_starProjection_ne_zero_norm_le_of_dualMinimum (M : Submodule ℤ E) [hMd : DiscreteTopology M]
    (hspan : span ℝ (M : Set E) = ⊤) {l : ℝ} (hl : 0 < l)
    (hdual : ∀ y : E, y ≠ 0 → (∀ x ∈ M, ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → l ≤ ‖y‖)
    (W : Submodule ℝ E) (N : Submodule ℤ E) (hNM : N ≤ M) (hNW : span ℝ (N : Set E) = W)
    (hW : W ≠ ⊤) :
    ∃ m ∈ M, Wᗮ.starProjection m ≠ 0 ∧
      ‖Wᗮ.starProjection m‖ ≤ (finrank ℝ E : ℝ) / l := by sorry
