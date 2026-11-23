-- Prove2me | Theorems.Thm_Formalism_GM_M_SSD_kap_add
-- name    : Formalism.GM.M.SSD.kap_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:08.299909+00:00
-- url     : https://prove2.me/theorems/91a42adf-f437-4000-9d6b-359e7d322934
-- title:
--   SSD: kap add
-- statement:
--   The SSD construction uses the kap add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L299-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L299-L301

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

theorem Formalism.GM.M.SSD.kap_add (F : (τ →₀ ℕ) → (σ →₀ ℕ)) (hF : Function.Injective F) (Q Q' : MvPolynomial σ K) :
    kap F hF (Q + Q') = kap F hF Q + kap F hF Q' := by sorry
