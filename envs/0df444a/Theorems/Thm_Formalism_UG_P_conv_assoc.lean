-- Prove2me | Theorems.Thm_Formalism_UG_P_conv_assoc
-- name    : Formalism.UG.P.conv_assoc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:21.62729+00:00
-- url     : https://prove2.me/theorems/b88579f7-75ea-4715-a9dd-7f0ecf9563a4
-- title:
--   P: conv assoc
-- statement:
--   The P construction uses the conv assoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/HeckeAssoc.lean#L20-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/HeckeAssoc.lean#L20-L85

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AssocFin
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeAssoc
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
variable {G : Type} [Group G] (K : Subgroup G)

theorem Formalism.UG.P.conv_assoc (hK : IsCommensurated K) {k : Type} [CommRing k] (f₁ f₂ f₃ : G → k)
    (h₁ : FinDosetSupp K f₁) (h₂ : IsBiInv K f₂) (h₃ : IsBiInv K f₃) (h₃' : FinDosetSupp K f₃) :
    conv K (conv K f₁ f₂) f₃ = conv K f₁ (conv K f₂ f₃) := by sorry
