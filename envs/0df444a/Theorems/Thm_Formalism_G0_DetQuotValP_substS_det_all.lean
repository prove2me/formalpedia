-- Prove2me | Theorems.Thm_Formalism_G0_DetQuotValP_substS_det_all
-- name    : Formalism.G0.DetQuotValP.substS_det_all
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:24.758804+00:00
-- url     : https://prove2.me/theorems/64f10d48-7f32-47af-92ef-a16cbadb892e
-- title:
--   Det Quot Val P: subst S det all
-- statement:
--   The Det Quot Val P construction uses the subst S det all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetQuotVal.lean#L24-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetQuotVal.lean#L24-L45

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

theorem Formalism.G0.DetQuotValP.substS_det_all {L : Type} [Field L] [Algebra K L] {r : ℕ} (hr : 1 ≤ r) (vec : ι → Bool)
    (S : Finset ι) (A : Fin r → ι) (hv : ∀ l, vec (A l) = true) (hS : ∀ l, A l ∈ S)
    (g : GL (Fin r) L) :
    substS (K := K) vec S g (detLetters A) =
      MvPolynomial.C Polynomial.X * Matrix.det (Matrix.of fun (l b : Fin r) =>
          (MvPolynomial.X (A l, b) : MvPolynomial (ι × Fin r) (Polynomial L))) := by sorry
