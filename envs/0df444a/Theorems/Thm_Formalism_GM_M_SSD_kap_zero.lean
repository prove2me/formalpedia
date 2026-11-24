-- Prove2me | Theorems.Thm_Formalism_GM_M_SSD_kap_zero
-- name    : Formalism.GM.M.SSD.kap_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:32.863092+00:00
-- url     : https://prove2.me/theorems/db141b41-892c-4c93-a37e-2a53f2027672
-- title:
--   SSD: kap zero
-- statement:
--   The SSD construction uses the kap zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L307-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L307-L309

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.SSD
open MvPolynomial Finset
variable {σ τ K : Type} [Field K] [DecidableEq σ]

theorem Formalism.GM.M.SSD.kap_zero (F : (τ →₀ ℕ) → (σ →₀ ℕ)) (hF : Function.Injective F) :
    kap F hF (0 : MvPolynomial σ K) = 0 := by sorry
