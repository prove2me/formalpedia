-- Prove2me | Theorems.Thm_Formalism_G0_AllButLESmithP_up
-- name    : Formalism.G0.AllButLESmithP.up
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:08:05.491814+00:00
-- url     : https://prove2.me/theorems/6888994e-17dd-4be1-b20b-358bdd3d6f8b
-- title:
--   All But LESmith P: up
-- statement:
--   The All But LESmith P construction uses the up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/AllButLESmith.lean#L56-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/AllButLESmith.lean#L56-L159

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

theorem Formalism.G0.AllButLESmithP.up (snf : Basis.SmithNormalForm P ι n) (π : O) (hπ : Irreducible π) (g E : ℕ)
    (S : Finset ι) (hS : ∀ i, snf.f i ∈ S → ¬ snf.a i ∣ π ^ E)
    (h : AllButLE π ⊤ P g E) : S.card ≤ g := by sorry
