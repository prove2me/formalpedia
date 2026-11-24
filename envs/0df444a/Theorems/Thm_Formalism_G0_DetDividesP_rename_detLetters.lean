-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_rename_detLetters
-- name    : Formalism.G0.DetDividesP.rename_detLetters
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:06:02.700808+00:00
-- url     : https://prove2.me/theorems/3e8f37da-de79-454d-ad7a-619a28135eed
-- title:
--   Det Divides P: rename det Letters
-- statement:
--   The Det Divides P construction uses the rename det Letters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L583-L585
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L583-L585

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

theorem Formalism.G0.DetDividesP.rename_detLetters (A : Fin r → ι) :
    rename Sum.inl (detLetters (K := K) A) = (Tm K A : Matrix (Fin r) (Fin r) (MvPolynomial ((ι × Fin r) ⊕ ι) K)).det := by sorry
