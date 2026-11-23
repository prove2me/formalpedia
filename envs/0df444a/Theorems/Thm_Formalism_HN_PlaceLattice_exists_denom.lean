-- Prove2me | Theorems.Thm_Formalism_HN_PlaceLattice_exists_denom
-- name    : Formalism.HN.PlaceLattice.exists_denom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:27.975809+00:00
-- url     : https://prove2.me/theorems/e23d9e28-636c-472f-85e4-26bcb1c1157a
-- title:
--   Place Lattice: exists denom
-- statement:
--   The Place Lattice construction uses the exists denom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DiscreteSpanOfLinIndep.lean#L224-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DiscreteSpanOfLinIndep.lean#L224-L248

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

theorem Formalism.HN.PlaceLattice.exists_denom {ι' : Type} [Fintype ι'] (e : ι' → V) (N : Submodule (𝓞 K) V) (hN : N.FG)
    (hsub : ∀ x ∈ N, x ∈ Submodule.span K (Set.range e)) :
    ∃ y : ℤ, y ≠ 0 ∧ N ≤ Submodule.span (𝓞 K) (Set.range fun a => ((y : K)⁻¹) • e a) := by sorry
