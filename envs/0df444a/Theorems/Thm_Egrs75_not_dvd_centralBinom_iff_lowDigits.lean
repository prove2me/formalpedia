-- Prove2me | Theorems.Thm_Egrs75_not_dvd_centralBinom_iff_lowDigits
-- name    : Egrs75.not_dvd_centralBinom_iff_lowDigits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:18.300928+00:00
-- url     : https://prove2.me/theorems/48427fdb-33b9-47a8-998e-3b159e5589db
-- title:
--   Egrs75: not dvd central Binom iff low Digits
-- statement:
--   **EGRS single-base bridge.** For an **odd prime** `p`,
--   `p ∤ C(2n,n)` exactly when every base-`p` digit of `n` is `≤ (p-1)/2`.
--   Kernel-clean: assembled from `coprime_centralBinom_prime_iff` + odd-prime digit
--   arithmetic. This is the per-prime Kummer fact the two-prime target stands on.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/Defs.lean#L86-L94
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/Defs.lean#L86-L94

module
public import Definitions.Def_LeanPool_Egrs75_CentralBinomialDigits
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_Defs
set_option autoImplicit true
@[expose] public section
public section
open Egrs75
open Nat

theorem Egrs75.not_dvd_centralBinom_iff_lowDigits {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (n : ℕ) : ¬ p ∣ Nat.centralBinom n ↔ LowDigits p n := by sorry
