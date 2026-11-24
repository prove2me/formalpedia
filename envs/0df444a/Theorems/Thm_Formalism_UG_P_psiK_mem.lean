-- Prove2me | Theorems.Thm_Formalism_UG_P_psiK_mem
-- name    : Formalism.UG.P.psiK_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:13.010409+00:00
-- url     : https://prove2.me/theorems/4aadc86f-8fe3-40af-8aa9-cb72f3701457
-- title:
--   P: psi K mem
-- statement:
--   The P construction uses the psi K mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/HeckeActionLevelMemHolds.lean#L15-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/HeckeActionLevelMemHolds.lean#L15-L32

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActionLevelMemHolds
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
variable {G₁ G₂ : Type} [Group G₁] [Group G₂]

theorem Formalism.UG.P.psiK_mem {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]
    {Γ : Subgroup (G₁ × G₂)} {K₁ : Subgroup G₁} {K₂ : Subgroup G₂}
    {ρK : Representation k (K₁.prod K₂) W}
    (hρ : ∀ κ : K₁.prod K₂, (κ : G₁ × G₂).2 = 1 → ρK κ = 1)
    {φ : G₁ × G₂ → W} (hφ : φ ∈ AMFK k Γ (K₁.prod K₂) ρK) (g : G₁ × G₂) :
    psiK φ g ∈ AMF k (⊥ : Subgroup G₁) K₁ (1 : Representation k (⊥ : Subgroup G₁) W) := by sorry
