-- Prove2me | Theorems.Thm_Formalism_ELL_QuadraticDifferenceHypotheses_qd_comm
-- name    : Formalism.ELL.QuadraticDifferenceHypotheses.qd_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:53.953363+00:00
-- url     : https://prove2.me/theorems/dbbfa3ac-7549-4c6e-a07c-77396b80ffe0
-- title:
--   Quadratic Difference Hypotheses: qd comm
-- statement:
--   The Quadratic Difference Hypotheses construction uses the qd comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IsogenyExpansion.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IsogenyExpansion.lean#L17-L18

import Definitions.Def_Formalism_EllipticTorsion_IsoExpand
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IsogenyExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.ELL Formalism.ELL.QuadraticDifferenceHypotheses
universe u
variable {O M Q : Type u} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup Q]

theorem Formalism.ELL.QuadraticDifferenceHypotheses.qd_comm (ψ : M → Q) (a b : M) : quadDiff ψ a b = quadDiff ψ b a := by sorry
