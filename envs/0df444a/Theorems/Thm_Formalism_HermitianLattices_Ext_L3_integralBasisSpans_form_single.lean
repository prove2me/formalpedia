-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_form_single
-- name    : Formalism.HermitianLattices.Ext.L3.integralBasisSpans.form_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:51:18.822127+00:00
-- url     : https://prove2.me/theorems/c900ce3b-ecaa-4f96-8704-5dd4ce5549b4
-- title:
--   integral Basis Spans: form single
-- statement:
--   The integral Basis Spans construction uses the form single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensitySixth.lean#L135-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensitySixth.lean#L135-L143

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

theorem Formalism.HermitianLattices.Ext.L3.integralBasisSpans.form_single {A : Type*} [CommRing A] [StarRing A] (N : Matrix κ κ A) (i j : κ) :
    star (Pi.single i (1 : A)) ⬝ᵥ (N *ᵥ Pi.single j (1 : A)) = N i j := by sorry
