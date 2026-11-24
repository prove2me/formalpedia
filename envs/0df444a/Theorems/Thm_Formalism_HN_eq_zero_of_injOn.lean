-- Prove2me | Theorems.Thm_Formalism_HN_eq_zero_of_injOn
-- name    : Formalism.HN.eq_zero_of_injOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:12.142828+00:00
-- url     : https://prove2.me/theorems/22fba2b7-27b9-40fc-a091-d23b002f6c36
-- title:
--   HN: eq zero of inj On
-- statement:
--   The HN construction uses the eq zero of inj On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SlopeIneq.lean#L231-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SlopeIneq.lean#L231-L233

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN

theorem Formalism.HN.eq_zero_of_injOn {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ρ : V →+ E} {L : Submodule R V}
    (hL : Set.InjOn ρ (L : Set V)) {x : V} (hx : x ∈ L) (h : ρ x = 0) : x = 0 := by sorry
