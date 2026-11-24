-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Rec_TraceQuadraticBound_psd_map
-- name    : Formalism.L2.Geo.Rec.TraceQuadraticBound.psd_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:56.59867+00:00
-- url     : https://prove2.me/theorems/12f79cfd-d4d9-4d36-a4e1-d11d1f3e3433
-- title:
--   Trace Quadratic Bound: psd map
-- statement:
--   The Trace Quadratic Bound construction uses the psd map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/ExistsStarMulSelf.lean#L116-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/ExistsStarMulSelf.lean#L116-L160

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Rec Formalism.L2.Geo.Rec.TraceQuadraticBound
variable {n : Type} [Fintype n] [DecidableEq n]
variable {K : Type} [Field K]

theorem Formalism.L2.Geo.Rec.TraceQuadraticBound.psd_map {m : ℕ} (cj : K → K) (σ : K →+* ℂ) (hσ : ∀ z, σ (cj z) = star (σ z)) (hd : DenseRange σ)
    (A : Matrix (Fin m) (Fin m) K) (hH : ∀ i k, A k i = cj (A i k))
    (hP : ∀ l : Fin m → K, l ≠ 0 → 0 < (σ (∑ i, ∑ k, l i * A i k * cj (l k))).re) :
    (A.map σ).PosSemidef ∧ (A.map σ).det ≠ 0 := by sorry
