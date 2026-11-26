-- Prove2me | Theorems.Thm_CSeparatedNPComplete_PolynomialCertificate_gadget_polynomial_certificate
-- name    : CSeparatedNPComplete.PolynomialCertificate.gadget_polynomial_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:57:37.51817+00:00
-- url     : https://prove2.me/theorems/4de74d97-1a41-452e-9298-be7e81380e6a
-- title:
--   Polynomial Certificate: gadget polynomial certificate
-- statement:
--   The original gadget predicate has a certificate of `d` bits, verified
--   within a quadratic binary-arithmetic work bound for the fixed-threshold Gaussian construction.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L235-L254
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PolynomialCertificate.lean#L235-L254

module
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Mathlib.Data.Nat.Size
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.PolynomialCertificate

theorem CSeparatedNPComplete.PolynomialCertificate.gadget_polynomial_certificate (d : ℕ) (s : Fin d → ℕ)
    (hd : 4 ≤ d) (hc : 1 ≤ dot (fun i => (s i : ℝ)) 1 / 2)
    (hs : perf_square_vec (fun i => (s i : ℝ))) :
    (∃ a : Vec d, box_constraints a ∧ dot a 1 = (d : ℝ) / 2 ∧
      hinge_form (dot (fun i => (s i : ℝ)) 1 / 2) a
        (partition_gadget_schedule d (fun i => (s i : ℝ))) ≤
        partition_schedule_threshold d (fun i => (s i : ℝ))) ↔
    ∃ b : Fin d → Bool, verify s b = true ∧
      (certificate b).length ≤ inputBits s ∧
      verificationWork s b ≤ 128 * (inputBits s + 1) ^ 2 := by sorry
