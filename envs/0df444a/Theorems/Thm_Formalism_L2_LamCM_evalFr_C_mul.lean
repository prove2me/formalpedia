-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_evalFr_C_mul
-- name    : Formalism.L2.LamCM.evalFr_C_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:19.714377+00:00
-- url     : https://prove2.me/theorems/1e90255e-9dc6-4f5d-90d6-e4700ba1b751
-- title:
--   Lam CM: eval Fr C mul
-- statement:
--   The Lam CM construction uses the eval Fr C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/LargeResidueExtensionLemma.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/LargeResidueExtensionLemma.lean#L59-L62

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

theorem Formalism.L2.LamCM.evalFr_C_mul {R : Type} [CommRing R] (a : R) (P : MvPolynomial (FrVar m) R)
    (Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R) : evalFr (C a * P) Y = a * evalFr P Y := by sorry
