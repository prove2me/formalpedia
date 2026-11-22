-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_orderedProd_smul_of_scalar_actions
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.orderedProd_smul_of_scalar_actions
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:29:11.194834+00:00
-- url     : https://prove2.me/theorems/775035ce-9baa-4cc3-a935-c15b43340cb7
-- title:
--   Height Descent Minors: ordered Prod smul of scalar actions
-- statement:
--   The Height Descent Minors construction uses the ordered Prod smul of scalar actions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1842-L1854
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1842-L1854

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable {k : Type} [CommRing k] {𝒰 : Type} [Ring 𝒰] [Algebra k 𝒰] {V : Type} [AddCommGroup V]
  [Module k V] [Module 𝒰 V] [IsScalarTower k 𝒰 V]

theorem Formalism.CohomologicalDescent.HeightDescentMinors.orderedProd_smul_of_scalar_actions (v : V) : ∀ (N : ℕ) (f : Fin N → 𝒰) (c : Fin N → k),
    (∀ j, f j • v = c j • v) → (List.ofFn f).prod • v = (∏ j, c j) • v := by sorry
