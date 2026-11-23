-- Prove2me | Theorems.Thm_Formalism_ELL_QuadraticDifferenceHypotheses_expand_mk
-- name    : Formalism.ELL.QuadraticDifferenceHypotheses.expand_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:24.583827+00:00
-- url     : https://prove2.me/theorems/5822eb36-1db8-4001-8d17-6b0df8d0a461
-- title:
--   Quadratic Difference Hypotheses: expand mk
-- statement:
--   The Quadratic Difference Hypotheses construction uses the expand mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IsogenyExpansion.lean#L87-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IsogenyExpansion.lean#L87-L114

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

theorem Formalism.ELL.QuadraticDifferenceHypotheses.expand_mk {N : AddSubgroup T} {bar : O → O} {nrm : O → S} {φ : M → T}
    (h : QuadHyp N bar nrm φ) (n m : ℕ) (y : Fin m → Fin n → O) (t : Fin m → M) :
    QuotientAddGroup.mk' N (∑ i, φ (∑ e, y e i • t e)) =
      QuotientAddGroup.mk' N ((∑ e, (∑ i, nrm (y e i)) • φ (t e))
        + (∑ e, ∑ e' ∈ Finset.univ.filter (fun e' => e < e'),
            quadDiff φ (t e) ((∑ i, bar (y e i) * y e' i) • t e'))) := by sorry
