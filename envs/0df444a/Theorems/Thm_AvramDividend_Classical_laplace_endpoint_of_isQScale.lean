-- Prove2me | Theorems.Thm_AvramDividend_Classical_laplace_endpoint_of_isQScale
-- name    : AvramDividend.Classical.laplace_endpoint_of_isQScale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T19:31:08.389104+00:00
-- url     : https://prove2.me/theorems/4e69df34-4496-4f93-85b6-4b1d4f14adfa
-- title:
--   Scale origin from a normalised Laplace endpoint limit
-- statement:
--   If a nonnegative continuous monotone scale function has the q=0 Laplace identity for large frequencies and the normalised Laplace transform tends to L, then its value at the origin is L.
-- source:
--   Lemma 8.6 corrected proof: change of variables u = beta*x and dominated convergence for the Laplace approximate identity.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem AvramDividend.Classical.laplace_endpoint_of_isQScale
    (ψ W : ℝ → ℝ) (β₀ L : ℝ)
    (hβ₀ : 0 < β₀) (hroot : Kyprianou.Ch08.Phi ψ 0 < β₀) (hL : L ≠ 0)
    (hs : Kyprianou.Ch08.IsQScale ψ 0 W)
    (hlim : Tendsto (fun β : ℝ => β * (ψ β)⁻¹) atTop (𝓝 L)) :
    W 0 = L := by sorry
