-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_quot_mem_pol
-- name    : Formalism.GM.GammaExpansion.quot_mem_pol
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:34.372135+00:00
-- url     : https://prove2.me/theorems/50de117c-af11-462e-8054-75e1c30d3dfa
-- title:
--   Gamma Expansion: quot mem pol
-- statement:
--   The Gamma Expansion construction uses the quot mem pol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L871-L898
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L871-L898

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

theorem Formalism.GM.GammaExpansion.quot_mem_pol (LL : M.Letters (N + 1)) (ρ : Fin r) (e : ℕ) (f h : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p])
    (hf : f ∈ M.Pol p r LL) (hh : ∀ m ∈ h.support, Finsupp.single (Fin.last N, ρ) e + m ∈ f.support) :
    h ∈ M.Pol p r (lowerLast LL e) := by sorry
