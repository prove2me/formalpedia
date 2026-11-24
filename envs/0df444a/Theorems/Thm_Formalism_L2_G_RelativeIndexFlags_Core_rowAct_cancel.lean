-- Prove2me | Theorems.Thm_Formalism_L2_G_RelativeIndexFlags_Core_rowAct_cancel
-- name    : Formalism.L2.G.RelativeIndexFlags.Core.rowAct_cancel
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:34:47.427572+00:00
-- url     : https://prove2.me/theorems/e34378b3-3953-4168-b1c3-72e0a987b59e
-- title:
--   Core: row Act cancel
-- statement:
--   The Core construction uses the row Act cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/IntegralWeylLatticeSpan/WeylEqSpanInt.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/IntegralWeylLatticeSpan/WeylEqSpanInt.lean#L42-L48

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Lemmata_GeneralBFactLeftSide_Imports
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_IntegralWeylLatticeSpan_WeylEqSpanInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.RelativeIndexFlags Formalism.L2.G.RelativeIndexFlags.Core

theorem Formalism.L2.G.RelativeIndexFlags.Core.rowAct_cancel {R : Type} [CommRing R] {r n : ℕ} (g gi : Matrix (Fin r) (Fin r) R) (h : gi * g = 1)
    (F : MvPolynomial (Fin r × Fin n) R) : rowAct R g (rowAct R gi F) = F := by sorry
