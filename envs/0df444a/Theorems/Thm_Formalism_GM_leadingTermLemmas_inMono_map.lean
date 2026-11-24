-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_inMono_map
-- name    : Formalism.GM.leadingTermLemmas.inMono_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:14.63365+00:00
-- url     : https://prove2.me/theorems/399b5b82-dbb8-452b-949e-8dacc66c9bc2
-- title:
--   leading Term Lemmas: in Mono map
-- statement:
--   The leading Term Lemmas construction uses the in Mono map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1792-L1794
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1792-L1794

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
variable (K : Type) [Field K] [CharZero K]
local notation "ι" => algebraMap ℚ K
variable {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)

theorem Formalism.GM.leadingTermLemmas.inMono_map {N : ℕ} (ρ : Fin r) (e : ℕ) (m : Fin (N + 1) × Fin r →₀ ℕ) :
    map ι (inMono (K := ℚ) ρ e m) = inMono (K := K) ρ e m := by sorry
