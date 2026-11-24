-- Prove2me | Theorems.Thm_Formalism_HN_QuotientRealization_psi_mem
-- name    : Formalism.HN.QuotientRealization.psi_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:09.133499+00:00
-- url     : https://prove2.me/theorems/5be16db8-d0e9-4689-bae1-4a3ec0bd6510
-- title:
--   Quotient Realization: psi mem
-- statement:
--   The Quotient Realization construction uses the psi mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/QuotRealize.lean#L218-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/QuotRealize.lean#L218-L228

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.QuotientRealization
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

theorem Formalism.HN.QuotientRealization.psi_mem [DecidableEq (InfinitePlace K)] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (S : Submodule (𝓞 K) V) (v : InfinitePlace K)
    (z : EuclideanSpace ℂ ι) (hz : z ∈ pv b X (Submodule.span K (S : Set V)) v) :
    PlaceDecomposition.psi v (WithLp.ofLp z) ∈ Submodule.span ℝ
      (zl (Formalism.HermitianLatticesTheory.realize b X) S : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) := by sorry
