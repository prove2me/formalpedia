-- Prove2me | Theorems.Thm_Formalism_ELL_QuadraticDifferenceHypotheses_expand
-- name    : Formalism.ELL.QuadraticDifferenceHypotheses.expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:25.35418+00:00
-- url     : https://prove2.me/theorems/6d54596a-c892-498d-80a9-ced4718d05d4
-- title:
--   Quadratic Difference Hypotheses: expand
-- statement:
--   The Quadratic Difference Hypotheses construction uses the expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IsogenyExpansion.lean#L31-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IsogenyExpansion.lean#L31-L54

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

theorem Formalism.ELL.QuadraticDifferenceHypotheses.expand {bar : O → O} {ψ : M → Q} (H : BiHyp bar ψ) {ι : Type*}
    [LinearOrder ι] (s : Finset ι) (x : ι → M) :
    ψ (∑ e ∈ s, x e) = ∑ e ∈ s, ψ (x e) +
      ∑ e ∈ s, ∑ e' ∈ s.filter (fun e' => e < e'), quadDiff ψ (x e) (x e') := by sorry
