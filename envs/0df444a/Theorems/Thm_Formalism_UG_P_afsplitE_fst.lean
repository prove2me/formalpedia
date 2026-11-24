-- Prove2me | Theorems.Thm_Formalism_UG_P_afsplitE_fst
-- name    : Formalism.UG.P.afsplitE_fst
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:34:27.643029+00:00
-- url     : https://prove2.me/theorems/24e697a6-fd18-43af-8353-c07c7f916907
-- title:
--   P: afsplit E fst
-- statement:
--   The P construction uses the afsplit E fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Afsplit.lean#L324-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Afsplit.lean#L324-L326

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

theorem Formalism.UG.P.afsplitE_fst (g : UPts σ J 𝔸) :
    (((afsplitE σ J v g).1 : UPts σ J (v.adicCompletion F)) : GL n _) =
      bc (prV (E := E) v) (g : GL n (E ⊗[F] 𝔸)) := by sorry
