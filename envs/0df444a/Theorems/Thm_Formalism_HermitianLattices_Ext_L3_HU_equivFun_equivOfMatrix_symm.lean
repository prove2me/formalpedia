-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_equivFun_equivOfMatrix_symm
-- name    : Formalism.HermitianLattices.Ext.L3.HU.equivFun_equivOfMatrix_symm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:34.017813+00:00
-- url     : https://prove2.me/theorems/20b3cfb0-9a3d-4f3f-bbb9-bd89f4dd433d
-- title:
--   HU: equiv Fun equiv Of Matrix symm
-- statement:
--   The HU construction uses the equiv Fun equiv Of Matrix symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EquivFunEquivOfMatrixSymm.lean#L103-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EquivFunEquivOfMatrixSymm.lean#L103-L104

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

theorem Formalism.HermitianLattices.Ext.L3.HU.equivFun_equivOfMatrix_symm (b : Basis κ K V) (G G' : Matrix κ κ K) (hG : G * G' = 1) (x : V) :
    b.equivFun ((equivOfMatrix b G G' hG).symm x) = G' *ᵥ b.equivFun x := by sorry
