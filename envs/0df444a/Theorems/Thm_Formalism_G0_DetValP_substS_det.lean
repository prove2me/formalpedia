-- Prove2me | Theorems.Thm_Formalism_G0_DetValP_substS_det
-- name    : Formalism.G0.DetValP.substS_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:31:00.331081+00:00
-- url     : https://prove2.me/theorems/7f072197-c12b-44fe-8282-84d1a6f3645e
-- title:
--   Det Val P: subst S det
-- statement:
--   The Det Val P construction uses the subst S det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetVal.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetVal.lean#L11-L18

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

theorem Formalism.G0.DetValP.substS_det {L : Type} [Field L] [Algebra K L] {r : ℕ} (vec : ι → Bool) (S : Finset ι)
    (g : GL (Fin r) L) (A : Fin r → ι) {R : Type} [CommRing R]
    (φ : MvPolynomial (ι × Fin r) (Polynomial L) →+* R) :
    φ (substS (K := K) vec S g (detLetters A)) =
      Matrix.det (Matrix.of fun l a => φ (substS (K := K) vec S g (MvPolynomial.X (A l, a)))) := by sorry
