-- Prove2me | Theorems.Thm_Formalism_L2_G_Triv_loc_lower
-- name    : Formalism.L2.G.Triv.loc_lower
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:20:10.557694+00:00
-- url     : https://prove2.me/theorems/5b860e04-8012-43b6-82d6-944907a6d7d0
-- title:
--   Triv: loc lower
-- statement:
--   The Triv construction uses the loc lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/FiniteStabAtOfLocal.lean#L162-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/FiniteStabAtOfLocal.lean#L162-L177

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_FiniteStabAtOfLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Triv
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
variable {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.L2.G.Triv.loc_lower (Λ : Submodule (𝓞 E) (n → E)) (m : ℤ) (hm : ∀ k, (Pi.single k (m : E) : n → E) ∈ Λ)
    (v : HeightOneSpectrum (𝓞 F)) (y : n → E ⊗[F] v.adicCompletion F) (hy : ∀ i, y i ∈ SV E v) :
    (fun i => inclE (F := F) (v.adicCompletion F) (m : E) * y i) ∈ latS (F := F) (v.adicCompletion F) (SV E v) Λ := by sorry
