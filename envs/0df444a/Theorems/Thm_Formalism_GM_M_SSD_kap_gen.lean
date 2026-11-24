-- Prove2me | Theorems.Thm_Formalism_GM_M_SSD_kap_gen
-- name    : Formalism.GM.M.SSD.kap_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:06.280091+00:00
-- url     : https://prove2.me/theorems/91307466-9d2e-4e14-9fa5-898034c9c61e
-- title:
--   SSD: kap gen
-- statement:
--   The SSD construction uses the kap gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L349-L354
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L349-L354

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
variable (e : τ → σ)

theorem Formalism.GM.M.SSD.kap_gen (he : Function.Injective e) (zm μ : σ →₀ ℕ) (hμ : ∀ x, μ (e x) = 0) (y : MvPolynomial τ K)
    (g : MvPolynomial σ K) (hg : ∀ w ∈ g.support, ∀ x, w (e x) = 0) :
    kap _ (F_inj e he zm μ) (monomial zm 1 * rename e y * g) = coeff μ g • y := by sorry
