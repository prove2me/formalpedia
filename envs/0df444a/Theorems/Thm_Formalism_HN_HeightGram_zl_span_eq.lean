-- Prove2me | Theorems.Thm_Formalism_HN_HeightGram_zl_span_eq
-- name    : Formalism.HN.HeightGram.zl_span_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:24:11.068315+00:00
-- url     : https://prove2.me/theorems/59b07b55-adbc-4342-85cf-38084ad75946
-- title:
--   Height Gram: zl span eq
-- statement:
--   The Height Gram construction uses the zl span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtGram.lean#L252-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtGram.lean#L252-L275

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Theorems.Thm_Formalism_HN_PlaceLattice_zl_span_eq

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
open Formalism.HN.HeightGram
variable {K : Type} [Field K] [NumberField K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.HN.HeightGram.zl_span_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (ρ : V →+ E) {ι' : Type} [Fintype ι'] (e : ι' → V) :
    zl ρ (Submodule.span (𝓞 K) (Set.range e)) =
      Submodule.span ℤ (Set.range fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι' =>
        ρ (integralBasis K p.1 • e p.2)) := by sorry
