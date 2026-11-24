-- Prove2me | Theorems.Thm_Formalism_G0_DetValP_part2
-- name    : Formalism.G0.DetValP.part2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:05.060221+00:00
-- url     : https://prove2.me/theorems/c6bf0a3a-b886-41bc-b0ef-1846c0ea0552
-- title:
--   Det Val P: part2
-- statement:
--   The Det Val P construction uses the part2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetVal.lean#L135-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetVal.lean#L135-L172

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetVal
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
open Formalism Formalism.G0 Formalism.G0.DetValP
open Formalism.G0
variable {K ι : Type} [Field K] [DecidableEq ι]

theorem Formalism.G0.DetValP.part2 {r : ℕ} (hr : 1 ≤ r) (vec : ι → Bool)
    (S : Finset ι) (A : Fin r → ι) (hA : Function.Injective A) (hv : ∀ l, vec (A l) = true)
    (hS : ¬ ∀ l, A l ∈ S) :
    ¬ MvPolynomial.C (Polynomial.X ^ 1) ∣
      substS (K := K) vec S (1 : GL (Fin r) K) (detLetters A) := by sorry
