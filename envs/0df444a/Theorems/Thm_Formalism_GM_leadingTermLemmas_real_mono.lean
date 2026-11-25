-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_real_mono
-- name    : Formalism.GM.leadingTermLemmas.real_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:50.753089+00:00
-- url     : https://prove2.me/theorems/1ff50bc2-5647-4cfb-bf6b-ce72b0bdbf9e
-- title:
--   leading Term Lemmas: real mono
-- statement:
--   The leading Term Lemmas construction uses the real mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1612-L1720
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1612-L1720

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
open MvPolynomial Finset Formalism.GM Filter Topology
variable {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)

theorem Formalism.GM.leadingTermLemmas.real_mono (hr : 1 ≤ r) (hv : LL.vec (Fin.last N) = true) (z e : ℕ)
    (m m' : Fin (N + 1) × Fin r →₀ ℕ) (hm : M.MultiDeg LL m) (hm' : M.MultiDeg LL m')
    (hme : e ≤ m (Fin.last N, ρ)) (hme' : e ≤ m' (Fin.last N, ρ)) :
    Tendsto (fun n : ℕ => gamK ℝ LL ρ z n (monomial m 1) (monomial m' 1) /
        (n : ℝ) ^ (LL.total + LL.deg (Fin.last N) - e)) atTop
      (𝓝 ((((e.factorial * (z + e).choose e : ℕ) : ℝ) * fk (inMono (K := ℝ) ρ e m) (inMono ρ e m')) /
        ((((LL.deg (Fin.last N)).factorial * LL.total.factorial : ℕ) : ℝ) * ∏ i, ((LL.deg i).factorial : ℝ)))) := by sorry
