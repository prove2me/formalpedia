-- Prove2me | Theorems.Thm_DetDLP_w1d_fp_exponent_readback
-- name    : DetDLP.w1d_fp_exponent_readback
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T02:02:32.333626+00:00
-- url     : https://prove2.me/theorems/2f4f43e1-7409-4f04-9d2b-86ec1f02aca8
-- title:
--   Prime-field Stage II readback from a certified canonical exponent
-- statement:
--   For a prime field and a generator, any accepted canonical discrete logarithm yields both the bounded scan certificate and, in the large regime, a native factor-block trace certificate for every reference factor base. No compatibility between the reference enumeration and the native seed is needed at readback time.

import Definitions.Def_DetDLP_W3_DriverReadback
import Theorems.Thm_DetDLP_w3_native_seed_coverage
import Theorems.Thm_DetDLP_w3_driver_trace_certificate

set_option autoImplicit false
open DetDLP

theorem DetDLP.w1d_fp_exponent_readback (p : ℕ) [Fact p.Prime] (h a : (ZMod p)ˣ) (gen : orderOf h = p-1)
    (accepts : ℕ → Prop) (u : ℕ) (hu : u < p-1) (powEq : h^u = a) (ok : accepts u) :
    w3_scanOutput (p-1) (Additive.ofMul h) (Additive.ofMul a) accepts ∧
    (∀ hg : w3_large p (p-1), letI : NeZero (p-1) := ⟨by have := hg.2.1; omega⟩
      ∀ F : Fin (blockCount (bitLen p)) → List (ZMod p)ˣ,
        ∃ (seed : FpSeed p (blockCount (bitLen p))) (B : Fin (blockCount (bitLen p)) → List (ZMod p)ˣ),
          (∀ i, (B i).Nodup ∧ (B i).toFinset = fpFactorBlock (hashThreshold p (p-1) (blockCount (bitLen p)) (p-1)) seed i) ∧
          w3_traceOutput (w3_fpFB F) (w3_fpFB B) (p-1) (Additive.ofMul h) (Additive.ofMul a) accepts) := by sorry
