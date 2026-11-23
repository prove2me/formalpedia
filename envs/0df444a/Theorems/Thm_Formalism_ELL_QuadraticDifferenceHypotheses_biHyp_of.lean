-- Prove2me | Theorems.Thm_Formalism_ELL_QuadraticDifferenceHypotheses_biHyp_of
-- name    : Formalism.ELL.QuadraticDifferenceHypotheses.biHyp_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:33.749069+00:00
-- url     : https://prove2.me/theorems/76fce9fa-b0e2-402d-a960-cdf561d04575
-- title:
--   Quadratic Difference Hypotheses: bi Hyp of
-- statement:
--   The Quadratic Difference Hypotheses construction uses the bi Hyp of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IsogenyExpansion.lean#L67-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IsogenyExpansion.lean#L67-L80

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

theorem Formalism.ELL.QuadraticDifferenceHypotheses.biHyp_of {N : AddSubgroup T} {bar : O → O} {nrm : O → S} {φ : M → T}
    (h : QuadHyp N bar nrm φ) : BiHyp bar (fun a => QuotientAddGroup.mk' N (φ a)) := by sorry
