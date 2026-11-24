-- Prove2me | Theorems.Thm_Formalism_G0_DetQuotValP_not_dvd_substS_det
-- name    : Formalism.G0.DetQuotValP.not_dvd_substS_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:12.843125+00:00
-- url     : https://prove2.me/theorems/688fa1af-f9c5-4967-9ab9-9d22b4a1c169
-- title:
--   Det Quot Val P: not dvd subst S det
-- statement:
--   The Det Quot Val P construction uses the not dvd subst S det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetQuotVal.lean#L90-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetQuotVal.lean#L90-L135

import Definitions.Def_Formalism_SubspaceCounting_DetQuotVal
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetVal
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetQuotVal
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
open Formalism Formalism.G0 Formalism.G0.DetQuotValP
open Formalism.G0 Formalism.G0.DetValP
variable {K ι : Type} [Field K] [DecidableEq ι]

theorem Formalism.G0.DetQuotValP.not_dvd_substS_det {L : Type} [Field L] [Algebra K L] {r : ℕ} (hr : 1 ≤ r)
    (vec : ι → Bool) (S : Finset ι) (A : Fin r → ι) (hA : Function.Injective A)
    (hv : ∀ l, vec (A l) = true) (hS : ¬ ∀ l, A l ∈ S) (g : GL (Fin r) L) :
    ¬ MvPolynomial.C Polynomial.X ∣ substS (K := K) vec S g (detLetters A) := by sorry
