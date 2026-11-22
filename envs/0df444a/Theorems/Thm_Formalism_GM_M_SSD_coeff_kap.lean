-- Prove2me | Theorems.Thm_Formalism_GM_M_SSD_coeff_kap
-- name    : Formalism.GM.M.SSD.coeff_kap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:43.57716+00:00
-- url     : https://prove2.me/theorems/12c87ee3-a252-4032-90cc-7e62fce14ece
-- title:
--   SSD: coeff kap
-- statement:
--   The SSD construction uses the coeff kap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L289-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L289-L297

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

theorem Formalism.GM.M.SSD.coeff_kap (F : (τ →₀ ℕ) → (σ →₀ ℕ)) (hF : Function.Injective F) (Q : MvPolynomial σ K) (n : τ →₀ ℕ) :
    coeff n (kap F hF Q) = coeff (F n) Q := by sorry
