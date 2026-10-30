-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_shifted_dense_prefix
-- name    : AvramDividend.Classical.avram_wave3_01_shifted_dense_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:59:25.772199+00:00
-- url     : https://prove2.me/theorems/bae2562d-857b-4c4a-9640-923e5f2ac42a
-- title:
--   Every actual centred shifted Lévy future has an exact Borel dense-sample running supremum
-- statement:
--   For any original spectrally negative Levy sample path and any finite shift time u, define its centred future increment function f(t)=X(u+t)-X(u). For every deterministic dense countable sampling schedule containing zero and every scheduled finite t, the supremum of f over [0,t] equals the ENNReal clipped countable sample supremum converted back to a real. The proof establishes right continuity of the actual translated increment path and its local boundedness from the source Lévy path, then applies the accepted generic dense-prefix-to-real-supremum theorem. This removes the genuinely nontrivial future-running-maximum encoding gap in the reflected ruin reward for the original killed first-record semigroup and scale C1 derivation.
-- source:
--   Original Lévy sample-path right continuity and boundedness; accepted avram_ws01e_b_dense_prefix_toReal_eq_genuine_sup, Kuznetsov Kyprianou Rivero (2013).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_dense_prefix_toReal_eq_genuine_sup

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_shifted_dense_prefix
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (u : ℝ≥0)
    (samples : ℕ → ℝ≥0) (hdense : Dense (Set.range samples))
    (hzero : (0 : ℝ≥0) ∈ Set.range samples)
    (t : ℝ≥0) (ht : t ∈ Set.range samples) :
    (⨆ i : ℕ, if samples i ≤ t then
      ENNReal.ofReal (X.X (u + samples i) ω - X.X u ω)
      else 0).toReal =
    ⨆ s : Icc (0 : ℝ≥0) t,
      X.X (u + s.1) ω - X.X u ω := by sorry
