-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_gam_oneSided
-- name    : Formalism.GM.GammaExpansion.gam_oneSided
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:42.453799+00:00
-- url     : https://prove2.me/theorems/d800bc9f-64e0-4192-8072-ba2c33328261
-- title:
--   Gamma Expansion: gam one Sided
-- statement:
--   The Gamma Expansion construction uses the gam one Sided property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L1063-L1143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L1063-L1143

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
variable (p : ℕ) [Fact p.Prime]

theorem Formalism.GM.GammaExpansion.gam_oneSided (N r : ℕ) (LL : M.Letters (N + 1)) (ρ : Fin r) (z e : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (hr : 1 ≤ r) (hvec : LL.vec (Fin.last N) = true)
    (hf : f ∈ M.Pol p r LL) (hord : ∀ m ∈ f.support, e ≤ m (Fin.last N, ρ)) (heo : e ≤ LL.deg (Fin.last N)) :
    IsPD LL.total (LL.total + LL.deg (Fin.last N) - e) (fun n => M.tieGam p LL ρ z n f f') := by sorry
