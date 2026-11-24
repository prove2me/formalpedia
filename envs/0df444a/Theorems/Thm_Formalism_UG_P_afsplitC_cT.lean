-- Prove2me | Theorems.Thm_Formalism_UG_P_afsplitC_cT
-- name    : Formalism.UG.P.afsplitC_cT
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:31:14.468745+00:00
-- url     : https://prove2.me/theorems/0452684b-5aae-4c7e-b0e3-71a36cec921e
-- title:
--   P: afsplit C c T
-- statement:
--   The P construction uses the afsplit C c T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitC.lean#L88-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitC.lean#L88-L93

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitC
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
variable {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n] (v : HeightOneSpectrum (𝓞 F))
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "Rv" => E ⊗[F] v.adicCompletion F
local notation "R" => E ⊗[F] 𝔸

theorem Formalism.UG.P.afsplitC_cT (σ : E →ₐ[F] E) (M : Matrix n n Rv) (N : Matrix n n R) :
    cT (sigR σ 𝔸) (afsplitC v M N) =
      afsplitC v (cT (sigR σ (v.adicCompletion F)) M) (cT (sigR σ 𝔸) N) := by sorry
