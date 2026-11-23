-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_norm_add_sq_eq_of_inner_eq_zero
-- name    : Formalism.NormUnitaryCountingLemmas.norm_add_sq_eq_of_inner_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:48.934474+00:00
-- url     : https://prove2.me/theorems/7218553a-4904-4022-81d5-0011edc175f3
-- title:
--   Norm Unitary Counting Lemmas: norm add sq eq of inner eq zero
-- statement:
--   The Norm Unitary Counting Lemmas construction uses the norm add sq eq of inner eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShortIndependentVectorsOfDualMinimum.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShortIndependentVectorsOfDualMinimum.lean#L81-L83

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

theorem Formalism.NormUnitaryCountingLemmas.norm_add_sq_eq_of_inner_eq_zero {x y : E} (h : inner ℝ x y = 0) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by sorry
