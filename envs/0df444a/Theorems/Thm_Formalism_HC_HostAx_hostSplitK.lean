-- Prove2me | Theorems.Thm_Formalism_HC_HostAx_hostSplitK
-- name    : Formalism.HC.HostAx.hostSplitK
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:44:32.316321+00:00
-- url     : https://prove2.me/theorems/d12d86c8-b3a6-5263-a501-3c42ebd32fbb
-- title:
--   Host Ax: host Split K
-- statement:
--   The Host Ax construction uses the host Split K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean#L322-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean#L322-L333

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.HostAx
variable {φ : Frame} (H : HostAx φ)

theorem Formalism.HC.HostAx.hostSplitK :
    (∀ p : ℕ, p.Prime →
      ((primesOver (span {(p : ℤ)}) (𝓞 H.K)).ncard = 2 ↔ (p = 2 ∨ (p ≠ 2 ∧ jacobiSym (-(H.d : ℤ)) p = 1)))) ∧
    (primesOver (span {(H.d : ℤ)}) (𝓞 H.K)).ncard = 1 ∧
    (primesOver (span {(H.q : ℤ)}) (𝓞 H.K)).ncard = 2 ∧
    ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P →
      (H.galE σ ∈ φ.Psi ↔ (primesOver (span {(p : ℤ)}) (𝓞 H.K)).ncard = 2) := by sorry
