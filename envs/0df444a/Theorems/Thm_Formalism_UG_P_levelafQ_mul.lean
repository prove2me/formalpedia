-- Prove2me | Theorems.Thm_Formalism_UG_P_levelafQ_mul
-- name    : Formalism.UG.P.levelafQ_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:31:25.401328+00:00
-- url     : https://prove2.me/theorems/2bfcf899-86d3-419e-89ce-e51b4f45c762
-- title:
--   P: levelaf Q mul
-- statement:
--   The P construction uses the levelaf Q mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelaf.lean#L246-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelaf.lean#L246-L253

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

theorem Formalism.UG.P.levelafQ_mul {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    {x y : 𝒜} (hx : levelafQ b x) (hy : levelafQ b y) : levelafQ b (x * y) := by sorry
