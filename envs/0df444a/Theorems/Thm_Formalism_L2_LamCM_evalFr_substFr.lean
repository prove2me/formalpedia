-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_evalFr_substFr
-- name    : Formalism.L2.LamCM.evalFr_substFr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:12.61584+00:00
-- url     : https://prove2.me/theorems/be553757-f96a-4638-9cfe-94dadbda3340
-- title:
--   Lam CM: eval Fr subst Fr
-- statement:
--   The Lam CM construction uses the eval Fr subst Fr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/LargeResidueExtensionLemma.lean#L37-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/LargeResidueExtensionLemma.lean#L37-L44

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

theorem Formalism.L2.LamCM.evalFr_substFr {R : Type} [CommRing R] (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R)
    (P : MvPolynomial (FrVar m) R) (Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R) :
    evalFr (substFr U P) Y = evalFr P (fun b => (U b).transpose * Y b) := by sorry
