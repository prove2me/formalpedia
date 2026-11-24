-- Prove2me | Theorems.Thm_Formalism_L2_Host_inertia_trivial
-- name    : Formalism.L2.Host.inertia_trivial
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:12:27.947751+00:00
-- url     : https://prove2.me/theorems/acdd79fb-777e-4f8a-a555-e8aff2670ecf
-- title:
--   Host: inertia trivial
-- statement:
--   The Host construction uses the inertia trivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/RamificationIdxEqOneOfNotDvd.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/RamificationIdxEqOneOfNotDvd.lean#L28-L31

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RamificationIdxEqOneOfNotDvd
import Theorems.Thm_Formalism_FrobeniusOrbits_Principal_inertia_trivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Ideal
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.BasicNotions Formalism.FrobeniusOrbits
variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem Formalism.L2.Host.inertia_trivial (p : ℕ) [Fact p.Prime] (hnd : ¬ p ∣ H.condN)
    (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E) :
    (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ σ = 1 := by sorry
