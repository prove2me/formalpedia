-- Prove2me | Theorems.Thm_Formalism_UG_P_conv_mul_right
-- name    : Formalism.UG.P.conv_mul_right
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:32:16.538667+00:00
-- url     : https://prove2.me/theorems/c70480ae-7f49-42ce-8b3a-0546f18cace0
-- title:
--   P: conv mul right
-- statement:
--   The P construction uses the conv mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/HeckeConvolutionMemHolds.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/HeckeConvolutionMemHolds.lean#L11-L18

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FiniteCosetsInDoset
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeConvolutionMemHolds
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
open Formalism.UG
variable {G : Type} [Group G]

theorem Formalism.UG.P.conv_mul_right {k : Type} [CommRing k] (K : Subgroup G) (f₁ f₂ : G → k)
    (hf₂ : IsBiInv K f₂) (g : G) (b : K) : conv K f₁ f₂ (g * b) = conv K f₁ f₂ g := by sorry
