-- Prove2me | Theorems.Thm_Formalism_G0_DetValP_substS_X
-- name    : Formalism.G0.DetValP.substS_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:30:54.486586+00:00
-- url     : https://prove2.me/theorems/934d5f59-bd4f-47df-b398-aae77e38106c
-- title:
--   Det Val P: subst S X
-- statement:
--   The Det Val P construction uses the subst S X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetVal.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetVal.lean#L20-L27

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

theorem Formalism.G0.DetValP.substS_X {L : Type} [Field L] [Algebra K L] {r : ℕ} (vec : ι → Bool) (S : Finset ι)
    (g : GL (Fin r) L) (p : ι × Fin r) :
    substS (K := K) vec S g (MvPolynomial.X p) =
      (if p.1 ∈ S then
      (if vec p.1 then ∑ b, MvPolynomial.C ((msMat g) p.2 b) * MvPolynomial.X (p.1, b)
       else ∑ b, MvPolynomial.C ((msDualMat g) p.2 b) * MvPolynomial.X (p.1, b))
    else MvPolynomial.X p) := by sorry
