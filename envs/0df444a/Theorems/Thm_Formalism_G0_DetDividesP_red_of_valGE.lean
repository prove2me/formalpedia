-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_red_of_valGE
-- name    : Formalism.G0.DetDividesP.red_of_valGE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:06:18.73124+00:00
-- url     : https://prove2.me/theorems/e9c5e717-e159-496f-bd89-b050d3d57429
-- title:
--   Det Divides P: red of val GE
-- statement:
--   The Det Divides P construction uses the red of val GE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L219-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L219-L288

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

theorem Formalism.G0.DetDividesP.red_of_valGE (_hr : 0 < r) (vec : ι → Bool) (S : Finset ι) (A : Fin r → ι) (d : ι → ℕ)
    (G : MvPolynomial (ι × Fin r) K) (th : ℕ)
    (hAS : ∀ l, A l ∈ S ∧ vec (A l) = true) (hG : MultiHom G d) (hV : ValGE vec S d G th)
    (hB : (∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) < th) :
    Red A G (th - ∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) := by sorry
