-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LP_lpa_joint
-- name    : Formalism.CohomologicalDescent.LP.lpa_joint
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:55:57.0541+00:00
-- url     : https://prove2.me/theorems/f0d5cce0-7b9d-4098-9857-3ef0114129bf
-- title:
--   LP: lpa joint
-- statement:
--   The LP construction uses the lpa joint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightDominantHolds.lean#L27-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightDominantHolds.lean#L27-L60

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLP
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightDominantHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LP
open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem Formalism.CohomologicalDescent.LP.lpa_joint {K N ι : Type*} [Field K] [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    (f : ι → Module.End K N) (hcomm : ∀ i j, Commute (f i) (f j))
    (hdiag : ∀ i, ⨆ μ : K, Module.End.eigenspace (f i) μ = ⊤) (s : Finset ι) (C : Submodule K N)
    (hC : ∀ i, ∀ x ∈ C, f i x ∈ C) (hne : C ≠ ⊥) :
    ∃ C' : Submodule K N, C' ≤ C ∧ C' ≠ ⊥ ∧ (∀ i, ∀ x ∈ C', f i x ∈ C') ∧ ∃ μ : ι → K, ∀ i ∈ s, ∀ x ∈ C', f i x = μ i • x := by sorry
