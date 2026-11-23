-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_tendsto_sum_ideal
-- name    : Formalism.HermitianLattices.Ext.L3.BoxSum.tendsto_sum_ideal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:27.790137+00:00
-- url     : https://prove2.me/theorems/af0ac8ba-acea-495a-984a-46c867960116
-- title:
--   Box Sum: tendsto sum ideal
-- statement:
--   The Box Sum construction uses the tendsto sum ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemIdealLatticeIff.lean#L129-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemIdealLatticeIff.lean#L129-L165

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

theorem Formalism.HermitianLattices.Ext.L3.BoxSum.tendsto_sum_ideal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {m : ℕ} (hm : 1 ≤ m)
    {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
        ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n ∈ I},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1))
      atTop (𝓝 ((m : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) / (Ideal.absNorm I : ℝ))) := by sorry
