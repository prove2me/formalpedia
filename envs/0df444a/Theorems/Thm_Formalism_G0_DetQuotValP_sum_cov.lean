-- Prove2me | Theorems.Thm_Formalism_G0_DetQuotValP_sum_cov
-- name    : Formalism.G0.DetQuotValP.sum_cov
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:04.046726+00:00
-- url     : https://prove2.me/theorems/0337453c-4aac-4d0e-bfea-896bcc982225
-- title:
--   Det Quot Val P: sum cov
-- statement:
--   The Det Quot Val P construction uses the sum cov property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetQuotVal.lean#L137-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetQuotVal.lean#L137-L141

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

theorem Formalism.G0.DetQuotValP.sum_cov {r : ℕ} (vec : ι → Bool) (S : Finset ι) (A : Fin r → ι)
    (hv : ∀ l, vec (A l) = true) (d : ι → ℕ) (m' : ℕ) :
    ∑ i ∈ S.filter (fun i => vec i = false), (d i + m' * (if i ∈ Set.range A then 1 else 0)) =
      ∑ i ∈ S.filter (fun i => vec i = false), d i := by sorry
