-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_integral_spanO
-- name    : Formalism.HermitianLattices.Ext.L3.Cell.integral_spanO
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:45:29.75821+00:00
-- url     : https://prove2.me/theorems/73a1bace-329e-4dd2-92bb-1aaf12518c99
-- title:
--   Cell: integral span O
-- statement:
--   The Cell construction uses the integral span O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/VdLeOneOfBasis.lean#L26-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/VdLeOneOfBasis.lean#L26-L36

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormalise
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdLeOneOfBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.Cell
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans WCA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)}

theorem Formalism.HermitianLattices.Ext.L3.Cell.integral_spanO {h : V →ₗ⋆[K] V →ₗ[K] K} {N : ℕ} (e : Basis (Fin N) K V) (A' : Fin N → 𝓞 F)
    (ho : ∀ i j, i ≠ j → h (e i) (e j) = 0) (hn : ∀ i, h (e i) (e i) = κ (ι (A' i))) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h (spanO e) := by sorry
