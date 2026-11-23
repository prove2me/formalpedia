-- Prove2me | Theorems.Thm_Formalism_ELL_QuadraticDifferenceHypotheses_mk_quadDiff
-- name    : Formalism.ELL.QuadraticDifferenceHypotheses.mk_quadDiff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:47.324584+00:00
-- url     : https://prove2.me/theorems/1b7da222-5ebf-4836-b2ba-4127ba9cec10
-- title:
--   Quadratic Difference Hypotheses: mk quad Diff
-- statement:
--   The Quadratic Difference Hypotheses construction uses the mk quad Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IsogenyExpansion.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IsogenyExpansion.lean#L62-L65

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
variable {O S M T : Type u} [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T]

theorem Formalism.ELL.QuadraticDifferenceHypotheses.mk_quadDiff (N : AddSubgroup T) (φ : M → T) (a b : M) :
    QuotientAddGroup.mk' N (quadDiff φ a b) =
      quadDiff (fun a => QuotientAddGroup.mk' N (φ a)) a b := by sorry
