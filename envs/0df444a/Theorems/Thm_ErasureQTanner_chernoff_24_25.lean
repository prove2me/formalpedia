-- Prove2me | Theorems.Thm_ErasureQTanner_chernoff_24_25
-- name    : ErasureQTanner.chernoff_24_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:08:23.776578+00:00
-- url     : https://prove2.me/theorems/a70abac1-e415-4289-941d-73ec026c7f5f
-- title:
--   (24)–(25) — Chernoff over the disjoint local views
-- statement:
--   Fix a code, $\rho\in[0,1]$ and $f>0$. If the local code $(C_A\otimes C_B)^\perp$ fails at $\rho$ with probability at most $f/(4\Delta)$, then
--   $$\Pr\Big[N_X\ge\frac{fN}{2\Delta^3}\Big]\le e^{-fN/(12\Delta^3)},$$
--   because the local views of distinct vertices of $V_{00}$ are disjoint, and the same holds for $N_Z$ with $(C_A^\perp\otimes D_B^\perp)^\perp$. Together with Theorem 15, Theorem 11 and the reduction it yields the failure bound of Theorem 16.
--
--   Differences from the source:
--   - reading: eq. (25) prints $n$ → $N$; reason: the paper calls (25) "the exact same argument" as (24); the proof has no other length here
--   - reading: a display with a law over $C_A,C_B$ → a fixed code and its per-view failure at $\rho$; reason: Theorem 11 applies per code (the remark on p.20); the code is chosen first
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), eqs. (24)–(25), p.29

import Mathlib
import Definitions.Def_QAlgorithms_Defs_TensorCode
import Definitions.Def_ErasureQTanner_LocalCodes
import Definitions.Def_ErasureQTanner_noisyProb
import Definitions.Def_ErasureQTanner_failCount

set_option autoImplicit false

open QAlgorithms

namespace ErasureQTanner

/-- **The Chernoff bound (24)–(25).** Pfister, Sprumont, Zémor, *Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels*, STOC 2027 submission (manuscript sha256 bf7a84a5…), p.29: "since on average we expect `≤ (N/∆²)·f(ρ,ε)/(4∆) = f(ρ,ε)N/(4∆³)` vertices of `V00` to have a decoding failure and since the
local views of any two distinct vertices `v, v′ ∈ V00` are disjoint, we have `Pr[N_X ≥ f(ρ,ε)N/(2∆³)] ≤ e^{−f(ρ,ε)N/(12∆³)}`", and the same for `N_Z`.

**Formalization Note.** For a fixed code: the per-view failure at `ρ` is at most `f/(4∆)` (the paper's display on p.29 draws the code at random; the paper's remark on Theorem 11, p.20, fixes it first). (25) prints `n` for `N`. -/
theorem chernoff_24_25 {Δ : ℕ} (hΔ : 0 < Δ) (Γ : LRData Δ) (L : LocalCodes Δ) (ρ f : ℝ)
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hf : 0 < f) :
    (noisyProb ρ (decodeFails (codeDual (tensorCode L.CA L.CB))) ≤ f / (4 * Δ) →
      noisyProb ρ (fun x : Γ.Square → Bool =>
          f * Γ.N / (2 * (Δ : ℝ) ^ 3) ≤ failCount Γ .v00 (codeDual (tensorCode L.CA L.CB)) x) ≤
        Real.exp (-(f * Γ.N / (12 * (Δ : ℝ) ^ 3)))) ∧
    (noisyProb ρ (decodeFails (codeDual (tensorCode (codeDual L.CA) (codeDual L.DB)))) ≤ f / (4 * Δ) →
      noisyProb ρ (fun x : Γ.Square → Bool =>
          f * Γ.N / (2 * (Δ : ℝ) ^ 3) ≤
            failCount Γ .v01 (codeDual (tensorCode (codeDual L.CA) (codeDual L.DB))) x) ≤
        Real.exp (-(f * Γ.N / (12 * (Δ : ℝ) ^ 3)))) := by sorry

end ErasureQTanner
