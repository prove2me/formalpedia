-- Prove2me | Theorems.Thm_Formalism_UG_P_afsplit_mulVec_mem
-- name    : Formalism.UG.P.afsplit_mulVec_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:34:18.189906+00:00
-- url     : https://prove2.me/theorems/8cc21d0b-4e70-48f1-baf7-19f9116bc25d
-- title:
--   P: afsplit mul Vec mem
-- statement:
--   The P construction uses the afsplit mul Vec mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Afsplit.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Afsplit.lean#L24-L27

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
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
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.afsplit_mulVec_mem (S : Subring A) (M : Matrix n n A) (hM : ∀ i j, M i j ∈ S) (x : n → A)
    (hx : ∀ i, x i ∈ S) (i : n) : (M *ᵥ x) i ∈ S := by sorry
