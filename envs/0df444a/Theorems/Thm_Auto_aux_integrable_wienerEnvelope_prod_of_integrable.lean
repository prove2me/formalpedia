-- Prove2me | Theorems.Thm_Auto_aux_integrable_wienerEnvelope_prod_of_integrable
-- name    : Auto.aux_integrable_wienerEnvelope_prod_of_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:48:41.809806+00:00
-- url     : https://prove2.me/theorems/3b07b308-31bd-5452-b736-90a8df4a8772
-- title:
--   Auto: aux integrable wiener Envelope prod of integrable
-- statement:
--   Radius-independence of envelope integrability for a product of Euclidean spaces.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1395-L1411
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1395-L1411

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_integrable_wienerEnvelope_prod_of_integrable {m l : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → 𝕜}
    (hf : Continuous f) {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s)
    (hfr : Integrable (wienerEnvelope f r)) :
    Integrable (wienerEnvelope f s) := by sorry
