-- Prove2me | Theorems.Thm_Formalism_UG_P_heckecomm_gelfand
-- name    : Formalism.UG.P.heckecomm_gelfand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:26.79902+00:00
-- url     : https://prove2.me/theorems/bb3b5899-620f-47ab-bc37-14451892fcff
-- title:
--   P: heckecomm gelfand
-- statement:
--   The P construction uses the heckecomm gelfand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Heckecomm.lean#L40-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Heckecomm.lean#L40-L70

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeConvolutionMemHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckecomm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G]

theorem Formalism.UG.P.heckecomm_gelfand {k : Type} [CommRing k] (K : Subgroup G) (θ : G → G)
    (hm : ∀ x y, θ (x * y) = θ y * θ x) (hi : ∀ x, θ (θ x) = x) (hK : ∀ x ∈ K, θ x ∈ K)
    (hdc : ∀ g, ∃ a b : K, θ g = (a : G) * g * b)
    (f₁ f₂ : G → k) (hf₁ : IsBiInv K f₁) (hf₂ : IsBiInv K f₂) :
    conv K f₁ f₂ = conv K f₂ f₁ := by sorry
