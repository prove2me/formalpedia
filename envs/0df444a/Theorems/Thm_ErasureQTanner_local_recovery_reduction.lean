-- Prove2me | Theorems.Thm_ErasureQTanner_local_recovery_reduction
-- name    : ErasureQTanner.local_recovery_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:03:29.545191+00:00
-- url     : https://prove2.me/theorems/564244b6-8c4d-4a7b-9146-5db34d5d1ba2
-- title:
--   Proof of Theorem 16, p.28 — the deterministic reduction to the adversarial decoder
-- statement:
--   Let $\varepsilon$ be an erasure pattern and $e_X,e_Z$ errors on it. Let $u_Z$ and $u_X$ be the parts of $e_Z$ and $e_X$ recovered by solving the local systems at $V_{00}$, $V_{01}$, and let $N_X$, $N_Z$ count the vertices that fail. Then:
--
--   1. $|e_X+u_X|\le\Delta^2N_Z$ and $|e_Z+u_Z|\le\Delta^2N_X$;
--   2. if $N_X,N_Z<f N/(2\Delta^3)$, then the two residual weights sum to less than $fN/\Delta$;
--   3. $H_X(e_Z+u_Z)^{\mathsf T}=H_Xe_Z^{\mathsf T}+H_Xu_Z^{\mathsf T}$, and likewise for $Z$, so the syndromes of the residuals are computable from the data;
--   4. a global syndrome bit of a check at $v$ is the inner product of its basis word with the restriction of $e$ to $Q(v)$;
--   5. the vector $e_v$ is the unique solution on the pattern exactly when the local pattern covers no non-zero word of the local dual tensor code.
--
--   This is what lets the worst-case decoder finish after the local step.
--
--   Differences from the source:
--   - reading: the sentence on $N_X$, $N_Z$, with recovery from "$\varepsilon$ and $H_ve_v^{\mathsf T}$" → five explicit clauses for every pattern and errors on it; reason: the unnumbered reduction, stated in full for a fixed code; the clause (23) is its union bound, carried by the goal
--   - encoding: any local view → $\Delta>0$; reason: with $\Delta=0$ there are no squares and the strict bound is meaningless
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), proof of Theorem 16 and footnote 1, p.28

import Mathlib
import Definitions.Def_QAlgorithms_Defs_TensorCode
import Definitions.Def_ErasureQTanner_HX
import Definitions.Def_ErasureQTanner_inputWords
import Definitions.Def_ErasureQTanner_failCount

set_option autoImplicit false

open QAlgorithms

namespace ErasureQTanner

/-- **The deterministic reduction in the proof of Theorem 16** (including footnote 1). Pfister, Sprumont, Zémor, *Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels*, STOC 2027 submission (manuscript sha256 bf7a84a5…), p.28: "If `N_X < f(ρ, ε)N/(2∆³)` and `N_Z < f(ρ, ε)N/(2∆³)`, the sum of the two
residual component weights is less than `f(ρ, ε)N/∆`". For a pattern `x` and errors supported on it, with `u_Z`, `u_X` the parts recovered at `V00`, `V01`:
the residuals `e_X + u_X`, `e_Z + u_Z` have weights at most `∆²N_Z`, `∆²N_X`; their syndromes are the sums of the given and the recovered ones; a global syndrome bit of a check
at `v` is the local syndrome of the view; and `e_v` is uniquely determined among vectors on the pattern exactly when the local covered subcode is zero. -/
theorem local_recovery_reduction {Δ : ℕ} (hΔ : 0 < Δ) (Γ : LRData Δ) (L : LocalCodes Δ) (x : Γ.Square → Bool)
    (eX eZ : Γ.Square → ZMod 2) (_heX : SupportedOn eX x) (_heZ : SupportedOn eZ x) (f : ℝ) :
    let C00 := codeDual (tensorCode L.CA L.CB)
    let C01 := codeDual (tensorCode (codeDual L.CA) (codeDual L.DB))
    let NX := failCount Γ .v00 C00 x
    let NZ := failCount Γ .v01 C01 x
    let uZ := recoveredPart Γ .v00 C00 x eZ
    let uX := recoveredPart Γ .v01 C01 x eX
    hammingNorm (eX + uX) ≤ Δ ^ 2 * NZ ∧
    hammingNorm (eZ + uZ) ≤ Δ ^ 2 * NX ∧
    ((NX : ℝ) < f * Γ.N / (2 * (Δ : ℝ) ^ 3) → (NZ : ℝ) < f * Γ.N / (2 * (Δ : ℝ) ^ 3) →
      ((hammingNorm (eX + uX) + hammingNorm (eZ + uZ) : ℕ) : ℝ) < f * Γ.N / Δ) ∧
    (HX Γ L).mulVec (eZ + uZ) = (HX Γ L).mulVec eZ + (HX Γ L).mulVec uZ ∧
    (HZ Γ L).mulVec (eX + uX) = (HZ Γ L).mulVec eX + (HZ Γ L).mulVec uX ∧
    (∀ (h : Γ.G) (i : Fin L.r00), (HX Γ L).mulVec eZ (Sum.inl (h, i)) =
      (L.b00 i : Fin Δ × Fin Δ → ZMod 2) ⬝ᵥ Γ.localVec .v00 h eZ) ∧
    (∀ (h : Γ.G) (i : Fin L.r01), (HZ Γ L).mulVec eX (Sum.inl (h, i)) =
      (L.b01 i : Fin Δ × Fin Δ → ZMod 2) ⬝ᵥ Γ.localVec .v01 h eX) ∧
    (∀ h : Γ.G, (∀ e e' : Fin Δ × Fin Δ → ZMod 2, SupportedOn e (Γ.localVec .v00 h x) →
        SupportedOn e' (Γ.localVec .v00 h x) →
        (∀ i, (L.b00 i : Fin Δ × Fin Δ → ZMod 2) ⬝ᵥ e = (L.b00 i : Fin Δ × Fin Δ → ZMod 2) ⬝ᵥ e') → e = e') ↔
      ¬ decodeFails C00 (Γ.localVec .v00 h x)) ∧
    (∀ h : Γ.G, (∀ e e' : Fin Δ × Fin Δ → ZMod 2, SupportedOn e (Γ.localVec .v01 h x) →
        SupportedOn e' (Γ.localVec .v01 h x) →
        (∀ i, (L.b01 i : Fin Δ × Fin Δ → ZMod 2) ⬝ᵥ e = (L.b01 i : Fin Δ × Fin Δ → ZMod 2) ⬝ᵥ e') → e = e') ↔
      ¬ decodeFails C01 (Γ.localVec .v01 h x)) := by sorry

end ErasureQTanner
