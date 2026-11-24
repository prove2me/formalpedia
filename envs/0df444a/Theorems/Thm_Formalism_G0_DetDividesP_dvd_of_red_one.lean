-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_dvd_of_red_one
-- name    : Formalism.G0.DetDividesP.dvd_of_red_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:06:20.329681+00:00
-- url     : https://prove2.me/theorems/8a97d8bd-9bca-442a-b93f-3313e578c155
-- title:
--   Det Divides P: dvd of red one
-- statement:
--   The Det Divides P construction uses the dvd of red one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L587-L698
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L587-L698

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
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

theorem Formalism.G0.DetDividesP.dvd_of_red_one (hr : 0 < r) (A : Fin r → ι) (hA : Function.Injective A)
    (G : MvPolynomial (ι × Fin r) K) (h : Red A G 1) : detLetters (K := K) A ∣ G := by sorry
