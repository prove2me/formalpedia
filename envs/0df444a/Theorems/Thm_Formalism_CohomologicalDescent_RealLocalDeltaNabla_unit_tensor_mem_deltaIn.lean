-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_unit_tensor_mem_deltaIn
-- name    : Formalism.CohomologicalDescent.RealLocalDeltaNabla.unit_tensor_mem_deltaIn
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:08:36.594501+00:00
-- url     : https://prove2.me/theorems/4a1cee21-3232-4b73-b74c-ad47204ede29
-- title:
--   Real Local Delta Nabla: unit tensor mem delta In
-- statement:
--   The Real Local Delta Nabla construction uses the unit tensor mem delta In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/RealLocalDeltaNabla.lean#L353-L364
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/RealLocalDeltaNabla.lean#L353-L364

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.RealLocalDeltaNabla
open Formalism.GradedWeylDivisibility Formalism.UG Formalism.RankGapBounds.JumpSetsAlt Formalism.RankGapBounds.FormsTensorLocalization Formalism.CohomologicalDescent.LA Formalism.CohomologicalDescent.SL2BinomialLattices

theorem Formalism.CohomologicalDescent.RealLocalDeltaNabla.unit_tensor_mem_deltaIn (O : Type) [CommRing O] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ)
    (z : ⨂[O] _ : Unit, ↥(deltaIn O r n hn ν)) :
    PiTensorProduct.subsingletonEquiv (R := O) (s := fun _ : Unit => ↥(dualWeyl O r n ν)) ()
      (PiTensorProduct.map (fun _ : Unit => (deltaIn O r n hn ν).subtype) z) ∈
        deltaIn O r n hn ν := by sorry
