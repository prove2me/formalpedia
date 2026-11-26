-- Prove2me | Theorems.Thm_Auto_MemW0_eLpNorm_toReal_le_wienerEnvelope
-- name    : Auto.MemW0.eLpNorm_toReal_le_wienerEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:48:34.182884+00:00
-- url     : https://prove2.me/theorems/fdc3f740-d369-54a6-b0c2-80ffa1e70214
-- title:
--   Mem W0: e Lp Norm to Real le wiener Envelope
-- statement:
--   If $f\in W_0(d)$ and $1\le p\le \infty$, then
--
--   $$
--   \|f\|_p\le C_{\text{P:lp-embedding},d}^{\frac 1p -1}\|f\|_{W_0}    \, .
--   $$
--
--   See also `Auto.MemW0.memLp`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1322-L1332
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1322-L1332

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.eLpNorm_toReal_le_wienerEnvelope {d : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : MemW0 f)
    {q : ℝ} (hq : 1 ≤ q) :
    (eLpNorm f (ENNReal.ofReal q) volume).toReal ≤
      volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) ^ (q⁻¹ - 1) *
        ∫ x, wienerEnvelope f 1 x := by sorry
