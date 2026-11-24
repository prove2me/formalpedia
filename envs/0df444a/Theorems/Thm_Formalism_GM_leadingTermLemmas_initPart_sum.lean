-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_initPart_sum
-- name    : Formalism.GM.leadingTermLemmas.initPart_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:11.856813+00:00
-- url     : https://prove2.me/theorems/89c201af-a70e-4f23-bfee-4cd10564ecad
-- title:
--   leading Term Lemmas: init Part sum
-- statement:
--   The leading Term Lemmas construction uses the init Part sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1830-L1835
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1830-L1835

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM

theorem Formalism.GM.leadingTermLemmas.initPart_sum (p : ℕ) [Fact p.Prime] {N r : ℕ} (ρ : Fin r) (e : ℕ)
    (f : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) :
    M.initPart (Fin.last N, ρ) e f = ∑ m ∈ f.support, f.coeff m • inMono (K := ℚ_[p]) ρ e m := by sorry
