-- Prove2me | Theorems.Thm_Formalism_UG_P_afsplit_sigR_IE
-- name    : Formalism.UG.P.afsplit_sigR_IE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:34:27.345955+00:00
-- url     : https://prove2.me/theorems/4efb271d-85a3-4e19-92f8-059ff00a3f04
-- title:
--   P: afsplit sig R IE
-- statement:
--   The P construction uses the afsplit sig R IE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitB.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitB.lean#L49-L54

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

theorem Formalism.UG.P.afsplit_sigR_IE (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    sigR σ 𝔸 (afsplitIE v x) = afsplitIE v (sigR σ (v.adicCompletion F) x) := by sorry
