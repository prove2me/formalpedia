-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a43_positive_taylor_mesh_small_large_energy_split
-- name    : AvramDividend.Classical.avram_ga_a43_positive_taylor_mesh_small_large_energy_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:05:14.379762+00:00
-- url     : https://prove2.me/theorems/002da31c-bd89-472e-a3a3-bab3ccf13ac5
-- title:
--   Finite physical Gaussian Taylor positive remainder energy splits into total energy and large-cell tail
-- statement:
--   For any finite set of Gaussian source mesh cells, positive Hessian-modulus coefficients that are small on small increments make the full quadratic Taylor remainder bounded by a small multiple of total quadratic energy plus a bounded multiple of large-increment energy.
-- source:
--   Original-process positive-only compact C2 Taylor analytic part of b0d9951c via Proved a39 and a41.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open BigOperators AvramDividend.Classical

theorem AvramDividend.Classical.avram_ga_a43_positive_taylor_mesh_small_large_energy_split {ι : Type*} (S : Finset ι) (a z : ι → ℝ)
    (ε M δ : ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hε : 0 ≤ ε)
    (hM : ∀ i ∈ S, a i ≤ M)
    (hSmall : ∀ i ∈ S, |z i| < δ → a i ≤ ε) :
    (∑ i ∈ S, a i * (z i)^2) ≤
      ε * (∑ i ∈ S, (z i)^2) +
        M * (∑ i ∈ S, if δ ≤ |z i| then (z i)^2 else 0) := by sorry
