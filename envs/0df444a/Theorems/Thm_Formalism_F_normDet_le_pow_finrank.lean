-- Prove2me | Theorems.Thm_Formalism_F_normDet_le_pow_finrank
-- name    : Formalism.F.normDet_le_pow_finrank
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:46.693505+00:00
-- url     : https://prove2.me/theorems/3e373e8a-a77e-4d65-8030-4703da451bb6
-- title:
--   F: norm Det le pow finrank
-- statement:
--   The F construction uses the norm Det le pow finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/GramDetLe.lean#L9-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/GramDetLe.lean#L9-L42

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_GramDetLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.F

theorem Formalism.F.normDet_le_pow_finrank {R F : Type*} [NormedAddCommGroup R] [InnerProductSpace ℝ R]
    [FiniteDimensional ℝ R] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (g : R →ₗ[ℝ] F) (K : ℝ) (hK : 0 ≤ K) (hg : ∀ y, ‖g y‖ ≤ K * ‖y‖) :
    g.normDet ≤ K ^ finrank ℝ R := by sorry
