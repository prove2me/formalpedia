-- Prove2me | Theorems.Thm_Formalism_ELL_QuadraticDifferenceHypotheses_sum1
-- name    : Formalism.ELL.QuadraticDifferenceHypotheses.sum1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:44.80998+00:00
-- url     : https://prove2.me/theorems/92522c5c-88a4-484c-a88d-3f3aa74bedcf
-- title:
--   Quadratic Difference Hypotheses: sum1
-- statement:
--   The Quadratic Difference Hypotheses construction uses the sum1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IsogenyExpansion.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IsogenyExpansion.lean#L20-L23

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

theorem Formalism.ELL.QuadraticDifferenceHypotheses.sum1 {bar : O → O} {ψ : M → Q} (H : BiHyp bar ψ) {ι : Type*}
    (s : Finset ι) (x : ι → M) (b : M) :
    quadDiff ψ (∑ e ∈ s, x e) b = ∑ e ∈ s, quadDiff ψ (x e) b := by sorry
