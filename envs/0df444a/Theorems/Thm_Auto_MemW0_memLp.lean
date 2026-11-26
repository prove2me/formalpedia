-- Prove2me | Theorems.Thm_Auto_MemW0_memLp
-- name    : Auto.MemW0.memLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:51:24.669919+00:00
-- url     : https://prove2.me/theorems/e6efa9a0-9915-510b-93b6-9b5e77e4e273
-- title:
--   Mem W0: mem Lp
-- statement:
--   **Proposition.**
--
--   Let $d\in \mathbb{N}$ be given and set
--
--   $$
--       C_{\text{P:lp-embedding},d}=\pi^{d/2}\Gamma(d/2+1)^{-1}\, .
--   $$
--
--   If $f\in W_0(d)$ and $1\le p\le \infty$, then
--
--   $$
--   \|f\|_p\le C_{\text{P:lp-embedding},d}^{\tfrac 1p -1}\|f\|_{W_0}    \, .
--   $$
--
--   See also `Auto.MemW0.memLp`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1090-L1125
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1090-L1125

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.MemW0.memLp {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : MemW0 f) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    MemLp f p volume := by sorry
