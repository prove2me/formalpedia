-- Prove2me | Theorems.Thm_Formalism_F_norm_sum_smul_le_of_int
-- name    : Formalism.F.norm_sum_smul_le_of_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:52.969414+00:00
-- url     : https://prove2.me/theorems/f7c150db-d225-43b5-bef3-bd6598db5a1c
-- title:
--   F: norm sum smul le of int
-- statement:
--   The F construction uses the norm sum smul le of int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/SlopeInequality.lean#L73-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/SlopeInequality.lean#L73-L109

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_GramDetLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopeInequality
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
open Formalism Formalism.F
universe u v

theorem Formalism.F.norm_sum_smul_le_of_int {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι] (v : ι → E) (w : ι → F)
    (C : ℝ) (h : ∀ n : ι → ℤ, ‖∑ i, (n i : ℝ) • w i‖ ≤ C * ‖∑ i, (n i : ℝ) • v i‖) :
    ∀ c : ι → ℝ, ‖∑ i, c i • w i‖ ≤ C * ‖∑ i, c i • v i‖ := by sorry
