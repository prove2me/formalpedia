-- Prove2me | Theorems.Thm_Formalism_G0_AllButLESmithP_pow_succ_dvd_of_not_dvd
-- name    : Formalism.G0.AllButLESmithP.pow_succ_dvd_of_not_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:56.458798+00:00
-- url     : https://prove2.me/theorems/70183cc2-a752-48d8-bc40-1c0fbf02ec60
-- title:
--   All But LESmith P: pow succ dvd of not dvd
-- statement:
--   The All But LESmith P construction uses the pow succ dvd of not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/AllButLESmith.lean#L16-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/AllButLESmith.lean#L16-L29

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

theorem Formalism.G0.AllButLESmithP.pow_succ_dvd_of_not_dvd {π : O} (hπ : Irreducible π) {a : O} {E : ℕ}
    (h : ¬ a ∣ π ^ E) : π ^ (E + 1) ∣ a := by sorry
