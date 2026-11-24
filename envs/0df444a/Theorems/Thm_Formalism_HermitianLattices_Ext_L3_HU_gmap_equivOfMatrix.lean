-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_gmap_equivOfMatrix
-- name    : Formalism.HermitianLattices.Ext.L3.HU.gmap_equivOfMatrix
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:39.782796+00:00
-- url     : https://prove2.me/theorems/11039ed9-471b-402e-9c55-682e1f99b7d1
-- title:
--   HU: gmap equiv Of Matrix
-- statement:
--   The HU construction uses the gmap equiv Of Matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EquivFunEquivOfMatrixSymm.lean#L116-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EquivFunEquivOfMatrixSymm.lean#L116-L133

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeZeroOfNotMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EquivFunEquivOfMatrixSymm
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

theorem Formalism.HermitianLattices.Ext.L3.HU.gmap_equivOfMatrix {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (b : Basis κ K V) (G G' : Matrix κ κ K)
    (hG : G * G' = 1) (h1 : Ent (SP K 𝔭) G) (h2 : Ent (SP K 𝔭) G') :
    Formalism.HermitianLatticesTheory.gmap (equivOfMatrix b G G' hG) (locF 𝔭 (spanO b)) = locF 𝔭 (spanO b) := by sorry
