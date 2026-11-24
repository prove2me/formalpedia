-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_q_etaDeg
-- name    : Formalism.GM.GammaExpansion.q_etaDeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:38.718795+00:00
-- url     : https://prove2.me/theorems/6be3ee57-2a29-4b6a-8517-ba5a149ddd7a
-- title:
--   Gamma Expansion: q eta Deg
-- statement:
--   The Gamma Expansion construction uses the q eta Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L1006-L1016
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L1006-L1016

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}

theorem Formalism.GM.GammaExpansion.q_etaDeg (LL : M.Letters (N + 1)) (ρ : Fin r) (e : ℕ) (he : e ≤ LL.deg (Fin.last N))
    (h : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (hh : h ∈ M.Pol p r (lowerLast LL e)) :
    ∀ s ∈ (aeval (M.freezeSub p LL ρ) h).support, s (Fin.last (N + 1), ρ) ≤ LL.total - e := by sorry
