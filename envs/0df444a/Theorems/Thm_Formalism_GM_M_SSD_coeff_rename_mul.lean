-- Prove2me | Theorems.Thm_Formalism_GM_M_SSD_coeff_rename_mul
-- name    : Formalism.GM.M.SSD.coeff_rename_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:29.607849+00:00
-- url     : https://prove2.me/theorems/8c725286-4538-44b5-b652-64d24ea69b07
-- title:
--   SSD: coeff rename mul
-- statement:
--   The SSD construction uses the coeff rename mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L313-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L313-L342

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

theorem Formalism.GM.M.SSD.coeff_rename_mul (he : Function.Injective e) (n : τ →₀ ℕ) (μ : σ →₀ ℕ) (hμ : ∀ x, μ (e x) = 0) (y : MvPolynomial τ K)
    (g : MvPolynomial σ K) (hg : ∀ w ∈ g.support, ∀ x, w (e x) = 0) :
    coeff (Finsupp.mapDomain e n + μ) (rename e y * g) = coeff n y * coeff μ g := by sorry
