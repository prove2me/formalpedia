-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_tsum_eq
-- name    : Formalism.HermitianLattices.Ext.L3.BoxSum.tsum_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:46:02.633964+00:00
-- url     : https://prove2.me/theorems/1c0064f0-e2b8-4fbf-b494-c07c5210db00
-- title:
--   Box Sum: tsum eq
-- statement:
--   The Box Sum construction uses the tsum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemIdealLatticeIff.lean#L88-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemIdealLatticeIff.lean#L88-L127

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

theorem Formalism.HermitianLattices.Ext.L3.BoxSum.tsum_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (m : ℕ) {I : Ideal (𝓞 F)}
    (hI : I ≠ ⊥) {N : ℝ} (hN : 0 < N) :
    ∑' x : ↑(sBox F ∩ N⁻¹ • (mixedEmbedding.idealLattice F (fracU hI) : Set (mixedEmbedding.mixedSpace F))), gW F m x =
      (∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F N ∧ n ∈ I},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1)) * N⁻¹ ^ (Formalism.HermitianLatticesTheory.fDeg K * (m - 1)) := by sorry
