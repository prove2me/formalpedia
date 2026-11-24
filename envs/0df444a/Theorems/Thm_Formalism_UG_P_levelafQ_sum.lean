-- Prove2me | Theorems.Thm_Formalism_UG_P_levelafQ_sum
-- name    : Formalism.UG.P.levelafQ_sum
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:33:22.773184+00:00
-- url     : https://prove2.me/theorems/e569deed-fa04-4602-b14f-ee5fd1509817
-- title:
--   P: levelaf Q sum
-- statement:
--   The P construction uses the levelaf Q sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelaf.lean#L232-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelaf.lean#L232-L234

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

theorem Formalism.UG.P.levelafQ_sum {m : ℕ} (b : Fin m → 𝓞 E) {ι : Type} (s : Finset ι) (f : ι → 𝒜)
    (h : ∀ i ∈ s, levelafQ b (f i)) : levelafQ b (∑ i ∈ s, f i) := by sorry
