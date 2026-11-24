-- Prove2me | Theorems.Thm_Formalism_G0_DetValP_part1b
-- name    : Formalism.G0.DetValP.part1b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:06.1889+00:00
-- url     : https://prove2.me/theorems/4ee5921a-d458-497a-8c6c-0bf55517620a
-- title:
--   Det Val P: part1b
-- statement:
--   The Det Val P construction uses the part1b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetVal.lean#L113-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetVal.lean#L113-L133

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

theorem Formalism.G0.DetValP.part1b {r : ℕ} (hr : 1 ≤ r) (vec : ι → Bool)
    (S : Finset ι) (A : Fin r → ι) (hA : Function.Injective A) (hv : ∀ l, vec (A l) = true)
    (hS : ∀ l, A l ∈ S) :
    ¬ MvPolynomial.C (Polynomial.X ^ 2) ∣
      substS (K := K) vec S (1 : GL (Fin r) K) (detLetters A) := by sorry
