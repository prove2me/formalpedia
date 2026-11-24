-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_sum_split
-- name    : Formalism.G0.DetDividesP.sum_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:06:15.93581+00:00
-- url     : https://prove2.me/theorems/eeb245ee-47c7-4f1a-985c-12b06628e4ff
-- title:
--   Det Divides P: sum split
-- statement:
--   The Det Divides P construction uses the sum split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L200-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L200-L217

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Polynomial
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

theorem Formalism.G0.DetDividesP.sum_split (vec : ι → Bool) (S : Finset ι) (A : Fin r → ι) (d : ι → ℕ)
    (hAS : ∀ l, A l ∈ S ∧ vec (A l) = true) :
    (∑ i ∈ S.filter (fun i => i ∉ Set.range A), d i) =
      (∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) +
        ∑ i ∈ S.filter (fun i => vec i = false), d i := by sorry
