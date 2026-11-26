-- Prove2me | Theorems.Thm_Auto_wienerNorm_le_max_one_three_mul_div_pow_mul
-- name    : Auto.wienerNorm_le_max_one_three_mul_div_pow_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:50:48.852637+00:00
-- url     : https://prove2.me/theorems/60e3b23b-1bda-4a0d-98ea-d095089b3963
-- title:
--   Auto: wiener Norm le max one three mul div pow mul
-- statement:
--   **Proposition.**
--
--   Let $d\in \mathbb{N}$.
--   Let $0<r,s<\infty$ and set
--
--   $$
--       C_{\text{W\_0 radius independence},d,r,s}=\max(1,(3s/r)^d)\, .
--   $$
--
--   Then for all continuous
--   $f:\mathbb{R}^d\to \mathbb{K}$ we have
--
--   $$
--       \|f\|_{W_0,s}\le C_{\text{W\_0 radius independence},d,r,s}\|f\|_{W_0,r}\, .
--   $$
--
--   In particular, for every $0<r<\infty$, a  continuous
--   $f:\mathbb{R}^d\to \mathbb{K}$ is in $W_0$ if and only if $\|f\|_{W_0,r}<\infty$.
--
--   See also `Auto.memW0_iff_integrable_wienerEnvelope`,
--   `Auto.wienerNorm_le_max_one_three_mul_div_pow_mul`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L916-L950
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L916-L950

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.wienerNorm_le_max_one_three_mul_div_pow_mul {d : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : Continuous f)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    wienerNorm f s ≤ ENNReal.ofReal (C_wienerNormRadiusIndependence d r s) * wienerNorm f r := by sorry
