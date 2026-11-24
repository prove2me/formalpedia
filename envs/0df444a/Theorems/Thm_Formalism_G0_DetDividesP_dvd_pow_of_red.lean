-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_dvd_pow_of_red
-- name    : Formalism.G0.DetDividesP.dvd_pow_of_red
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:06:10.703807+00:00
-- url     : https://prove2.me/theorems/9c3c1902-2194-44cd-b4f3-18d74d2eed7f
-- title:
--   Det Divides P: dvd pow of red
-- statement:
--   The Det Divides P construction uses the dvd pow of red property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L712-L724
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L712-L724

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
open Formalism.G0
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

theorem Formalism.G0.DetDividesP.dvd_pow_of_red (hr : 0 < r) (A : Fin r → ι) (hA : Function.Injective A) :
    ∀ (n : ℕ) (G : MvPolynomial (ι × Fin r) K), Red A G n → detLetters (K := K) A ^ n ∣ G := by sorry
