-- Prove2me | Theorems.Thm_Formalism_UG_P_afsplitE_symm
-- name    : Formalism.UG.P.afsplitE_symm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:33:29.858548+00:00
-- url     : https://prove2.me/theorems/16db7afe-8dc6-4f6a-90ac-bc92bde95120
-- title:
--   P: afsplit E symm
-- statement:
--   The P construction uses the afsplit E symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Afsplit.lean#L331-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Afsplit.lean#L331-L333

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
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E)
  (v : HeightOneSpectrum (𝓞 F))
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

theorem Formalism.UG.P.afsplitE_symm (p : UPts σ J (v.adicCompletion F) × afsplitKer σ J v) :
    (((afsplitE σ J v).symm p : UPts σ J 𝔸) : GL n (E ⊗[F] 𝔸)) =
      afsplitU v (p.1 : GL n (E ⊗[F] v.adicCompletion F)) (p.2 : GL n (E ⊗[F] 𝔸)) := by sorry
