-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_fock_init_bil
-- name    : Formalism.GM.leadingTermLemmas.fock_init_bil
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:16.455804+00:00
-- url     : https://prove2.me/theorems/7417f3fc-1988-40ba-a8b8-331b73867403
-- title:
--   leading Term Lemmas: fock init bil
-- statement:
--   The leading Term Lemmas construction uses the fock init bil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1837-L1844
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1837-L1844

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

theorem Formalism.GM.leadingTermLemmas.fock_init_bil (p : ℕ) [Fact p.Prime] {N r : ℕ} (ρ : Fin r) (e : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) :
    M.fock p (M.initPart (Fin.last N, ρ) e f) (M.initPart (Fin.last N, ρ) e f') =
      ∑ m ∈ f.support, ∑ m' ∈ f'.support, f.coeff m * f'.coeff m' * fk (inMono (K := ℚ_[p]) ρ e m) (inMono ρ e m') := by sorry
