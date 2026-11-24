-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_CubicFlow_cubic_roots
-- name    : Formalism.L2.Th1.A.CubicFlow.cubic_roots
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:53.884804+00:00
-- url     : https://prove2.me/theorems/bd25df09-f1c5-4fe5-9af8-8ee85e427f36
-- title:
--   Cubic Flow: cubic roots
-- statement:
--   The Cubic Flow construction uses the cubic roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FlowThird.lean#L54-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FlowThird.lean#L54-L68

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTwo
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowThird
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.CubicFlow
open QuadraticFlow
variable {A : Type u} [CommRing A]

theorem Formalism.L2.Th1.A.CubicFlow.cubic_roots [IsDomain A] {C3 C2 C1 C0 z1 z2 z3 : A} (hz : z1 ≠ z2)
    (h1 : C3 * z1 ^ 3 + C2 * z1 ^ 2 + C1 * z1 + C0 = 0)
    (h2 : C3 * z2 ^ 3 + C2 * z2 ^ 2 + C1 * z2 + C0 = 0)
    (he1 : C3 * (z1 + z2 + z3) + C2 = 0) :
    C3 * z3 ^ 3 + C2 * z3 ^ 2 + C1 * z3 + C0 = 0 ∧
      C3 * (z1 * z2 + z1 * z3 + z2 * z3) - C1 = 0 ∧ C3 * (z1 * z2 * z3) + C0 = 0 := by sorry
