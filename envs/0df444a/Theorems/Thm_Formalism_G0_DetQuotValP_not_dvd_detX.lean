-- Prove2me | Theorems.Thm_Formalism_G0_DetQuotValP_not_dvd_detX
-- name    : Formalism.G0.DetQuotValP.not_dvd_detX
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:21.313338+00:00
-- url     : https://prove2.me/theorems/c62b1576-4ac3-4826-99d0-39aad46907d3
-- title:
--   Det Quot Val P: not dvd det X
-- statement:
--   The Det Quot Val P construction uses the not dvd det X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetQuotVal.lean#L47-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetQuotVal.lean#L47-L69

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

theorem Formalism.G0.DetQuotValP.not_dvd_detX {L : Type} [Field L] {r : ℕ} (A : Fin r → ι) (hA : Function.Injective A) :
    ¬ (MvPolynomial.C Polynomial.X : MvPolynomial (ι × Fin r) (Polynomial L)) ∣
      Matrix.det (Matrix.of fun (l b : Fin r) =>
          (MvPolynomial.X (A l, b) : MvPolynomial (ι × Fin r) (Polynomial L))) := by sorry
