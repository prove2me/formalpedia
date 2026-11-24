-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_form_mulVec
-- name    : Formalism.HermitianLattices.Ext.L3.integralBasisSpans.form_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:55.498662+00:00
-- url     : https://prove2.me/theorems/9e6928e0-ef4d-4e1b-ba9a-fb9506cc2b60
-- title:
--   integral Basis Spans: form mul Vec
-- statement:
--   The integral Basis Spans construction uses the form mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensitySixth.lean#L131-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensitySixth.lean#L131-L133

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.integralBasisSpans
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable [Fact (IsFixF K F)]

theorem Formalism.HermitianLattices.Ext.L3.integralBasisSpans.form_mulVec {A : Type*} [CommRing A] [StarRing A] (M N : Matrix κ κ A) (u v : κ → A) :
    star (M *ᵥ u) ⬝ᵥ (N *ᵥ (M *ᵥ v)) = star u ⬝ᵥ ((Mᴴ * N * M) *ᵥ v) := by sorry
