-- Prove2me | Theorems.Thm_Formalism_G0_AllButLESmithP_key
-- name    : Formalism.G0.AllButLESmithP.key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:44:36.306276+00:00
-- url     : https://prove2.me/theorems/615760fa-dce9-4f73-b923-287054577258
-- title:
--   All But LESmith P: key
-- statement:
--   The All But LESmith P construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/AllButLESmith.lean#L161-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/AllButLESmith.lean#L161-L191

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

theorem Formalism.G0.AllButLESmithP.key (snf : Basis.SmithNormalForm P ι n) (π : O) (hπ : Irreducible π) (g E : ℕ)
    (B : Finset (Fin n)) (hB : ∀ i, i ∈ B ↔ ¬ snf.a i ∣ π ^ E) :
    AllButLE π ⊤ P g E ↔ B.card + (Fintype.card ι - n) ≤ g := by sorry
