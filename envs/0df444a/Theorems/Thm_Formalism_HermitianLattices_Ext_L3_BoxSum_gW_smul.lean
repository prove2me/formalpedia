-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_gW_smul
-- name    : Formalism.HermitianLattices.Ext.L3.BoxSum.gW_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:46:59.949728+00:00
-- url     : https://prove2.me/theorems/fd9abdc8-f94d-41df-a0ac-68a5f930200b
-- title:
--   Box Sum: g W smul
-- statement:
--   The Box Sum construction uses the g W smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemIdealLatticeIff.lean#L77-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemIdealLatticeIff.lean#L77-L86

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoTsumDivPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormEqProdOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemIdealLatticeIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology MeasureTheory Pointwise
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem Formalism.HermitianLattices.Ext.L3.BoxSum.gW_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (m : ℕ) {T : ℝ} {n : 𝓞 F}
    (hn : n ∈ boxSet K F T) (c : ℝ) :
    gW F m (c • mixedEmbedding F (n : F)) =
      (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * c ^ (Formalism.HermitianLatticesTheory.fDeg K * (m - 1)) := by sorry
