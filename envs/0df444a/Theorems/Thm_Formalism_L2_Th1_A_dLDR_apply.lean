-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
-- name    : Formalism.L2.Th1.A.dLDR_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:33.295822+00:00
-- url     : https://prove2.me/theorems/d624c5a5-a0bc-4fc3-b6c7-9bd123cec797
-- title:
--   A: d LDR apply
-- statement:
--   The A construction uses the d LDR apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/Laurent.lean#L207-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/Laurent.lean#L207-L207

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
variable {R : Type u} [CommRing R]

theorem Formalism.L2.Th1.A.dLDR_apply (f : LaurentSeries R) : dLDR R f = dL f := by sorry

attribute [defeq] Formalism.L2.Th1.A.dLDR_apply
