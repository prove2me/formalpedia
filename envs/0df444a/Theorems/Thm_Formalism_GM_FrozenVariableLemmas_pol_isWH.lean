-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableLemmas_pol_isWH
-- name    : Formalism.GM.FrozenVariableLemmas.pol_isWH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:42.647075+00:00
-- url     : https://prove2.me/theorems/f1066ed6-2b6c-4b31-88f9-856d95ff1136
-- title:
--   Frozen Variable Lemmas: pol is WH
-- statement:
--   The Frozen Variable Lemmas construction uses the pol is WH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L53-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L53-L60

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableLemmas
open MvPolynomial Finset

theorem Formalism.GM.FrozenVariableLemmas.pol_isWH (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (G : Fin N → ℕ)
    {f : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hf : f ∈ M.Pol p r LL) :
    IsWeightedHomogeneous (fun x : Fin N × Fin r => G x.1) f (∑ b, G b * LL.deg b) := by sorry
