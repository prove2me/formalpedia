-- Prove2me | Theorems.Thm_Formalism_GM_M_SSD_absSat
-- name    : Formalism.GM.M.SSD.absSat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:39.862054+00:00
-- url     : https://prove2.me/theorems/0fd43e30-2c12-4f38-b026-673044958bdf
-- title:
--   SSD: abs Sat
-- statement:
--   The SSD construction uses the abs Sat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L246-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L246-L272

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

theorem Formalism.GM.M.SSD.absSat (V : ι' → Submodule K (MvPolynomial σ K)) (a : ι' → ι → ℕ) (ha : Function.Injective a)
    (C : AddSubgroup K) (T : AddSubgroup (MvPolynomial σ K))
    (h1 : ∀ L, ∀ v ∈ V L, ∀ m ∈ v.support, sd sv m ≤ a L)
    (hT : ∀ f ∈ T, ∀ m, coeff m f ∈ C)
    (h2 : ∀ L, ∀ v ∈ V L, (∀ m, sd sv m = a L → coeff m v ∈ C) → v ∈ T)
    (s : Finset ι') (v : ι' → MvPolynomial σ K) (hv : ∀ L ∈ s, v L ∈ V L)
    (hC : ∀ m, coeff m (∑ L ∈ s, v L) ∈ C) : ∑ L ∈ s, v L ∈ T := by sorry
