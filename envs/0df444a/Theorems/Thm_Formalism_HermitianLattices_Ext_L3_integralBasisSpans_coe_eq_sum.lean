-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_coe_eq_sum
-- name    : Formalism.HermitianLattices.Ext.L3.integralBasisSpans.coe_eq_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:51:30.312627+00:00
-- url     : https://prove2.me/theorems/b76fb700-48ea-45ca-a435-f18973cbd73c
-- title:
--   integral Basis Spans: coe eq sum
-- statement:
--   The integral Basis Spans construction uses the coe eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensitySixth.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensitySixth.lean#L27-L33

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

theorem Formalism.HermitianLattices.Ext.L3.integralBasisSpans.coe_eq_sum (b : Basis κ K V) (y : spanO b) :
    (y : V) = ∑ i, algebraMap (𝓞 K) K (crd b y i) • b i := by sorry
