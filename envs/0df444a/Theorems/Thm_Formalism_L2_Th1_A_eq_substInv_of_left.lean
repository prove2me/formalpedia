-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_eq_substInv_of_left
-- name    : Formalism.L2.Th1.A.eq_substInv_of_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:51.927798+00:00
-- url     : https://prove2.me/theorems/e59bf68f-5b3d-4c36-b857-36cc72c39bfc
-- title:
--   A: eq subst Inv of left
-- statement:
--   The A construction uses the eq subst Inv of left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/CompInv.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/CompInv.lean#L24-L31

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
variable {R : Type u} [CommRing R]

theorem Formalism.L2.Th1.A.eq_substInv_of_left (s : R⟦X⟧) (h0 : constantCoeff s = 0) (h1 : IsUnit (coeff 1 s))
    (t : R⟦X⟧) (ht : t.subst s = X) :
    t = s.substInvOfIsUnit h1 := by sorry
