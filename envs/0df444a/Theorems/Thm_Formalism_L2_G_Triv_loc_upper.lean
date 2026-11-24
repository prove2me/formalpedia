-- Prove2me | Theorems.Thm_Formalism_L2_G_Triv_loc_upper
-- name    : Formalism.L2.G.Triv.loc_upper
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:20:35.723248+00:00
-- url     : https://prove2.me/theorems/f24b19a2-47b9-4fcb-b799-f1e486deeabe
-- title:
--   Triv: loc upper
-- statement:
--   The Triv construction uses the loc upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/FiniteStabAtOfLocal.lean#L144-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/FiniteStabAtOfLocal.lean#L144-L160

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

theorem Formalism.L2.G.Triv.loc_upper (Λ : Submodule (𝓞 E) (n → E)) (m : ℤ) (hm : ∀ x ∈ Λ, ∀ k, IsIntegral ℤ ((m : E) * x k))
    (v : HeightOneSpectrum (𝓞 F)) (y : n → E ⊗[F] v.adicCompletion F)
    (hy : y ∈ latS (F := F) (v.adicCompletion F) (SV E v) Λ) (i : n) :
    inclE (F := F) (v.adicCompletion F) (m : E) * y i ∈ SV E v := by sorry
