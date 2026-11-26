-- Prove2me | Theorems.Thm_Auto_integrable_wienerEnvelope_iff
-- name    : Auto.integrable_wienerEnvelope_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:47:14.755366+00:00
-- url     : https://prove2.me/theorems/97947951-c5ba-4b02-9153-3021c06c8d69
-- title:
--   Auto: integrable wiener Envelope iff
-- statement:
--   In particular, for every $0<r<\infty$, a continuous
--   $f:\mathbb{R}^d\to \mathbb{K}$ is in $W_0$ if and only if $\|f\|_{W_0,r}<\infty$.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L818-L824
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L818-L824

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.integrable_wienerEnvelope_iff {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : Continuous f) {r s : ℝ} (hr : 0 < r)
    (hs : 0 < s) :
    Integrable (wienerEnvelope f r) ↔ Integrable (wienerEnvelope f s) := by sorry
