-- Prove2me | Theorems.Thm_Formalism_UG_P_afsplitC_int
-- name    : Formalism.UG.P.afsplitC_int
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:34:57.695141+00:00
-- url     : https://prove2.me/theorems/37f4cd04-8541-4713-bd20-d808acc16e4f
-- title:
--   P: afsplit C int
-- statement:
--   The P construction uses the afsplit C int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Afsplit.lean#L197-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Afsplit.lean#L197-L204

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
  (v : HeightOneSpectrum (𝓞 F))
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
variable {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.afsplitC_int (M : Matrix n n (E ⊗[F] v.adicCompletion F)) (N : Matrix n n (E ⊗[F] 𝔸))
    (hM : ∀ i j, M i j ∈ tensInt (F := F) (v.adicCompletion F) (intOE E)
      (v.adicCompletionIntegers F).toSubring)
    (hN : ∀ i j, N i j ∈ tensInt (F := F) 𝔸 (intOE E) (intAd F)) (i j : n) :
    afsplitC v M N i j ∈ tensInt (F := F) 𝔸 (intOE E) (intAd F) := by sorry
