-- Prove2me | Theorems.Thm_Auto_aux_integrable_wienerEnvelope_of_integrable
-- name    : Auto.aux_integrable_wienerEnvelope_of_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:43:40.805584+00:00
-- url     : https://prove2.me/theorems/6fadde0e-c18e-4931-9be1-f73e765bfd68
-- title:
--   Auto: aux integrable wiener Envelope of integrable
-- statement:
--   Integrability of the local envelope is independent of its positive radius.  The finite cover
--   of a compact ball gives the comparison, and translation-invariance of Lebesgue measure makes each
--   summand integrable.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L799-L812
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L799-L812

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_integrable_wienerEnvelope_of_integrable {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : Continuous f) {r s : ℝ} (hr : 0 < r)
    (hs : 0 ≤ s) (hfr : Integrable (wienerEnvelope f r)) :
    Integrable (wienerEnvelope f s) := by sorry
