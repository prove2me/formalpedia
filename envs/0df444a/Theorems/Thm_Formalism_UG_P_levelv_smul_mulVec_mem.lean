-- Prove2me | Theorems.Thm_Formalism_UG_P_levelv_smul_mulVec_mem
-- name    : Formalism.UG.P.levelv_smul_mulVec_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:33:16.209001+00:00
-- url     : https://prove2.me/theorems/ffb6bfc8-584d-4795-aec9-00eff26a2b62
-- title:
--   P: levelv smul mul Vec mem
-- statement:
--   The P construction uses the levelv smul mul Vec mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelv.lean#L223-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelv.lean#L223-L232

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
open IsDedekindDomain NumberField
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.levelv_smul_mulVec_mem (N : ℕ) (M : Matrix n n (E ⊗[F] v.adicCompletion F))
    (hM : ∀ i j, N • M i j ∈ lvS F E v) (x : n → E ⊗[F] v.adicCompletion F)
    (hx : x ∈ stdLat (n := n) ↥(lvS F E v)) :
    N • (M *ᵥ x) ∈ stdLat (n := n) ↥(lvS F E v) := by sorry
