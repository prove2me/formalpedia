-- Prove2me | Theorems.Thm_Auto_memW0_iff_integrable_wienerEnvelope
-- name    : Auto.memW0_iff_integrable_wienerEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:51:01.934022+00:00
-- url     : https://prove2.me/theorems/a058b848-27ac-43d1-a3e6-6752a27cf6cf
-- title:
--   Auto: mem W0 iff integrable wiener Envelope
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
--   See also `Auto.wienerNorm_le_max_one_three_mul_div_pow_mul`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L974-L982
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L974-L982

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.memW0_iff_integrable_wienerEnvelope {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : Continuous f) {r : ℝ} (hr : 0 < r) :
    MemW0 f ↔ Integrable (wienerEnvelope f r) := by sorry
