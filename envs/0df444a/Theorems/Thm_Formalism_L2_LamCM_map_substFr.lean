-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_map_substFr
-- name    : Formalism.L2.LamCM.map_substFr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:13.179426+00:00
-- url     : https://prove2.me/theorems/7ce47a38-1d21-440b-94d7-d7358d2d9f53
-- title:
--   Lam CM: map subst Fr
-- statement:
--   The Lam CM construction uses the map subst Fr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/LargeResidueExtensionLemma.lean#L51-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/LargeResidueExtensionLemma.lean#L51-L57

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

theorem Formalism.L2.LamCM.map_substFr {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R)
    (P : MvPolynomial (FrVar m) R) :
    MvPolynomial.map f (substFr U P) = substFr (fun b => (U b).map f) (MvPolynomial.map f P) := by sorry
