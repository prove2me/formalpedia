-- Prove2me | Theorems.Thm_Formalism_HN_PlaceLattice_rk_span_eq
-- name    : Formalism.HN.PlaceLattice.rk_span_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:55.127796+00:00
-- url     : https://prove2.me/theorems/c30fec1c-36c2-4dce-9563-bd22aa12e4a1
-- title:
--   Place Lattice: rk span eq
-- statement:
--   The Place Lattice construction uses the rk span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DiscreteSpanOfLinIndep.lean#L216-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DiscreteSpanOfLinIndep.lean#L216-L222

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PlaceLattice
variable {K : Type} [Field K] [NumberField K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.HN.PlaceLattice.rk_span_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (ρ : V →+ E) (hρ : Function.Injective ρ) {ι' : Type} [Fintype ι']
    (e : ι' → V) (he : LinearIndependent K e) :
    rk ρ (Submodule.span (𝓞 K) (Set.range e)) = Module.finrank ℚ K * Fintype.card ι' := by sorry
