-- Prove2me | Theorems.Thm_Formalism_UG_P_conv_finDosetSupp
-- name    : Formalism.UG.P.conv_finDosetSupp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:21.288795+00:00
-- url     : https://prove2.me/theorems/5106a690-bfbe-4658-886c-37645b1eebc1
-- title:
--   P: conv fin Doset Supp
-- statement:
--   The P construction uses the conv fin Doset Supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/HeckeConvolutionMemHolds.lean#L48-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/HeckeConvolutionMemHolds.lean#L48-L76

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

theorem Formalism.UG.P.conv_finDosetSupp {k : Type} [CommRing k] {K : Subgroup G} (hK : IsCommensurated K)
    (f₁ f₂ : G → k) (hs₁ : FinDosetSupp K f₁) (hs₂ : FinDosetSupp K f₂) :
    FinDosetSupp K (conv K f₁ f₂) := by sorry
