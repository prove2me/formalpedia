-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_exists_adapted_basis_alt
-- name    : Formalism.LatticeBaseChangeAlt.exists_adapted_basis_alt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:51.408562+00:00
-- url     : https://prove2.me/theorems/743bf52c-9c51-44f9-8c86-00c379687f6e
-- title:
--   Lattice Base Change Alt: exists adapted basis alt
-- statement:
--   The Lattice Base Change Alt construction uses the exists adapted basis alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/ExistsSmulMemOfMemSpan.lean#L18-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/ExistsSmulMemOfMemSpan.lean#L18-L97

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Lemmata_MiscLemmasO_Imports
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_ExistsSmulMemOfMemSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module

theorem Formalism.LatticeBaseChangeAlt.exists_adapted_basis_alt (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    (M : Submodule O V) (V' : Submodule K V) (hM : Formalism.LatticeIndexTer.IsLat O K V M) :
    ∃ (b : Basis (Fin (finrank K V)) K V) (s : Set (Fin (finrank K V))),
      M ≤ Submodule.span O (Set.range b) ∧ (∀ i ∈ s, b i ∈ M ∧ b i ∈ V') ∧
        V' ≤ Submodule.span K (b '' s) := by sorry
