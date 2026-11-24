-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_CC_Surj_wal_lower
-- name    : Formalism.MainNotions.Gaps.CC.Surj.wal_lower
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:57:16.215323+00:00
-- url     : https://prove2.me/theorems/b7445024-e51c-441a-9914-be43f7f73f86
-- title:
--   Surj: wal lower
-- statement:
--   The Surj construction uses the wal lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ClassCountWaLat.lean#L206-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ClassCountWaLat.lean#L206-L245

import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ClassCountWaLat
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.CC Formalism.MainNotions.Gaps.CC.Surj
open Formalism.UG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : Type} [Fintype n] [DecidableEq n]
local notation "Av" => E ⊗[F] v.adicCompletion F
local notation "Sv" => Formalism.UG.P.lvS F E v
local notation "ιv" => inclE (F := F) (E := E) (v.adicCompletion F)

theorem Formalism.MainNotions.Gaps.CC.Surj.wal_lower (Λ : Submodule (𝓞 E) (n → E))
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ x : n → Av, (∀ i, x i ∈ Sv) →
      (fun i => (m : Av) * x i) ∈ latS (F := F) (v.adicCompletion F) Sv Λ := by sorry
