-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_substFr_substFr
-- name    : Formalism.L2.LamCM.substFr_substFr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:43.779288+00:00
-- url     : https://prove2.me/theorems/01086a31-fa17-490d-9520-6ec9bd899527
-- title:
--   Lam CM: subst Fr subst Fr
-- statement:
--   The Lam CM construction uses the subst Fr subst Fr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/LargeResidueExtensionLemma.lean#L27-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/LargeResidueExtensionLemma.lean#L27-L35

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementS
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsEvalNeZeroOfTotalDegreeLt
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsMonicIrreducibleCardGt
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_LargeResidueExtensionLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open MvPolynomial IsLocalRing
variable {B : Type} {m : B → ℕ}

theorem Formalism.L2.LamCM.substFr_substFr {R : Type} [CommRing R] (U U' : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R)
    (P : MvPolynomial (FrVar m) R) : substFr U (substFr U' P) = substFr (fun b => U b * U' b) P := by sorry
