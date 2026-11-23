-- Prove2me | Theorems.Thm_Formalism_ELL_QuadraticDifferenceHypotheses_sum2
-- name    : Formalism.ELL.QuadraticDifferenceHypotheses.sum2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:19:02.163182+00:00
-- url     : https://prove2.me/theorems/4d030a3f-14b3-42a0-87cf-b4b1d1f09496
-- title:
--   Quadratic Difference Hypotheses: sum2
-- statement:
--   The Quadratic Difference Hypotheses construction uses the sum2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IsogenyExpansion.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IsogenyExpansion.lean#L25-L29

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

theorem Formalism.ELL.QuadraticDifferenceHypotheses.sum2 {bar : O → O} {ψ : M → Q} (H : BiHyp bar ψ) {ι : Type*}
    (s : Finset ι) (x : ι → M) (a : M) :
    quadDiff ψ a (∑ e ∈ s, x e) = ∑ e ∈ s, quadDiff ψ a (x e) := by sorry
