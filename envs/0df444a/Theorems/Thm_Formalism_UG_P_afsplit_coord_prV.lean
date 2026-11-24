-- Prove2me | Theorems.Thm_Formalism_UG_P_afsplit_coord_prV
-- name    : Formalism.UG.P.afsplit_coord_prV
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:30:40.12769+00:00
-- url     : https://prove2.me/theorems/38e8d4a1-6086-412a-8084-ac468b769c7b
-- title:
--   P: afsplit coord pr V
-- statement:
--   The P construction uses the afsplit coord pr V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitB.lean#L114-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitB.lean#L114-L123

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitB
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
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

theorem Formalism.UG.P.afsplit_coord_prV (b : Module.Basis (Module.Free.ChooseBasisIndex F E) F E)
    (i : Module.Free.ChooseBasisIndex F E) (w : HeightOneSpectrum (𝓞 F)) (y : E ⊗[F] 𝔸) :
    TensorProduct.lid F (w.adicCompletion F) ((b.coord i).rTensor _ (prV (E := E) w y)) =
      (TensorProduct.lid F 𝔸 ((b.coord i).rTensor _ y)) w := by sorry
