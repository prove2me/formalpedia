-- Prove2me | Theorems.Thm_Formalism_UG_P_conv_biInv
-- name    : Formalism.UG.P.conv_biInv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:28:39.024215+00:00
-- url     : https://prove2.me/theorems/bec2845c-ff6a-4499-85b0-d0083033b141
-- title:
--   P: conv bi Inv
-- statement:
--   The P construction uses the conv bi Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/HeckeConvolutionMemHolds.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/HeckeConvolutionMemHolds.lean#L43-L46

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

theorem Formalism.UG.P.conv_biInv {k : Type} [CommRing k] (K : Subgroup G) (f₁ f₂ : G → k)
    (hf₁ : IsBiInv K f₁) (hf₂ : IsBiInv K f₂) : IsBiInv K (conv K f₁ f₂) := by sorry
