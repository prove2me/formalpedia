-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_supp_of_supported
-- name    : Formalism.L2.FormalSeriesBounds.rtj_supp_of_supported
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:24:48.1748+00:00
-- url     : https://prove2.me/theorems/078a0db9-1c3d-4090-a679-e67e28daadb6
-- title:
--   Formal Series Bounds: rtj supp of supported
-- statement:
--   The Formal Series Bounds construction uses the rtj supp of supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L66-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L66-L70

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {σ : Type}

theorem Formalism.L2.FormalSeriesBounds.rtj_supp_of_supported {A : Set σ} {P : MvPolynomial σ K} (hP : P ∈ MvPolynomial.supported K A)
    (m : σ →₀ ℕ) (hm : MvPolynomial.coeff m P ≠ 0) : (↑m.support : Set σ) ⊆ A := by sorry
