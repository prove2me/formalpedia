-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_raw_cuboid_jumpEnergy_eq_endpointEnergy
-- name    : Auto.aux_CuboidNorm.raw_cuboid_jumpEnergy_eq_endpointEnergy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:42:45.747704+00:00
-- url     : https://prove2.me/theorems/ef783f1a-b543-41e6-ab38-61bd3438b251
-- title:
--   aux Cuboid Norm: raw cuboid jump Energy eq endpoint Energy
-- statement:
--   Re-express the raw-coordinate jump energy used by the cuboid calculation
--   as the `ctEndpointEnergy` of its Euclidean lifts.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2031-L2053
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2031-L2053

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]

theorem Auto.aux_CuboidNorm.raw_cuboid_jumpEnergy_eq_endpointEnergy {n J : ℕ}
    (N : Fin (J + 1) → ℕ) (a : Fin n → ZVector n → ℝ)
    (ε δ : ℝ) :
    (∑ j : Fin J, eLpNorm
      (fun x ↦ ctTwistedAverageAtScale (N j.succ : ℝ) ctUnitIntervalKernel
          (fun i ↦ aux_liftRaw (aux_cuboidEmbed ε δ i (a i)))
          (WithLp.toLp 2 x) -
        ctTwistedAverageAtScale (N j.castSucc : ℝ) ctUnitIntervalKernel
          (fun i ↦ aux_liftRaw (aux_cuboidEmbed ε δ i (a i)))
          (WithLp.toLp 2 x)) 2 volume ^ 2) =
      ctEndpointEnergy J (fun q ↦ (N q : ℝ)) ctUnitIntervalKernel
        (fun i ↦ aux_liftRaw (aux_cuboidEmbed ε δ i (a i))) := by sorry
