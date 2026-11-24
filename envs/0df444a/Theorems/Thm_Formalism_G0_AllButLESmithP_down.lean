-- Prove2me | Theorems.Thm_Formalism_G0_AllButLESmithP_down
-- name    : Formalism.G0.AllButLESmithP.down
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:06:12.358812+00:00
-- url     : https://prove2.me/theorems/fa9e4c2c-1555-417f-ae41-7805e1902cc0
-- title:
--   All But LESmith P: down
-- statement:
--   The All But LESmith P construction uses the down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/AllButLESmith.lean#L33-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/AllButLESmith.lean#L33-L54

import Definitions.Def_Formalism_SubspaceCounting_StatementD
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_AllButLESmith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open Formalism Formalism.G0
open Formalism.G0.AllButLESmithP
variable {O M ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [AddCommGroup M] [Module O M] [Fintype ι]
variable {P : Submodule O M} {n : ℕ}

theorem Formalism.G0.AllButLESmithP.down (snf : Basis.SmithNormalForm P ι n) (π : O) (g E : ℕ) (S : Finset ι)
    (hS : ∀ j, j ∉ S → ∃ i, snf.f i = j ∧ snf.a i ∣ π ^ E) (hcard : S.card ≤ g) :
    AllButLE π ⊤ P g E := by sorry
