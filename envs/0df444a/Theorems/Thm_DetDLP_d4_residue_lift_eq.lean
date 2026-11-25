-- Prove2me | Theorems.Thm_DetDLP_d4_residue_lift_eq
-- name    : DetDLP.d4_residue_lift_eq
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T08:28:15.82079+00:00
-- url     : https://prove2.me/theorems/2aab655d-76e8-4fb0-9b29-ea81f0537cf1
-- title:
--   Canonical residues are unchanged by increasing precision
-- statement:
--   Let the defining polynomial be monic, and let the target precision be at least the source precision. Reinterpreting each canonical coefficient at the larger modulus leaves the entire serialized residue unchanged. For a base tensor with coefficients below the target modulus, the serialized extension element replaces every coefficient by a block of length equal to the polynomial degree, with that coefficient in position zero and all other positions zero. Degree zero contributes an empty block.
-- source:
--   Concrete source interface M14-StoppedSrc, item 2; definitions DetDLP.AppendixD4.lift and DetDLP.AppendixD4.residue.

import Definitions.Def_DetDLP_D4StoppedNode
set_option autoImplicit false
open Polynomial DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle DetDLP.D4StoppedNode
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.d4_residue_lift_eq (f : ℤ[X]) (l p q : ℕ) (hf : f.Monic) (hpq : p ≤ q) :
    (∀ z : B f l p, residue f l q hf (lift hf q z) = residue f l p hf z) ∧
    (∀ a : Fin l → ℕ, (∀ j, a j < 2^q) → residue f l q hf (liftBase f l q a) =
      encodeNatListBin (pad f.natDegree (List.ofFn a))) := by sorry
