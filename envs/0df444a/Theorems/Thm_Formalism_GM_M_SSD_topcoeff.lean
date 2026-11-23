-- Prove2me | Theorems.Thm_Formalism_GM_M_SSD_topcoeff
-- name    : Formalism.GM.M.SSD.topcoeff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:58.462106+00:00
-- url     : https://prove2.me/theorems/e6c0e749-1214-41c9-a8a2-1fac85716fa9
-- title:
--   SSD: topcoeff
-- statement:
--   The SSD construction uses the topcoeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L207-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L207-L218

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
variable {σ ι K ι' : Type} [Field K] [DecidableEq σ] [Fintype ι] (sv : ι → σ)

theorem Formalism.GM.M.SSD.topcoeff (a : ι' → ι → ℕ) (ha : Function.Injective a) (P : ι' → MvPolynomial σ K → Prop)
    (h1 : ∀ L v, P L v → ∀ m ∈ v.support, sd sv m ≤ a L)
    (s : Finset ι') (v : ι' → MvPolynomial σ K) (hv : ∀ L ∈ s, P L (v L)) (L : ι') (hL : L ∈ s)
    (hmax : ∀ L' ∈ s, ∑ k, a L' k ≤ ∑ k, a L k) (m : σ →₀ ℕ) (hm : sd sv m = a L) :
    coeff m (∑ L' ∈ s, v L') = coeff m (v L) := by sorry
