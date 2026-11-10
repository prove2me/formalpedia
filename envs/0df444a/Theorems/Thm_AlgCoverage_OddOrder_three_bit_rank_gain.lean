-- Prove2me | Theorems.Thm_AlgCoverage_OddOrder_three_bit_rank_gain
-- name    : AlgCoverage.OddOrder.three_bit_rank_gain
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:45:31.7052+00:00
-- url     : https://prove2.me/theorems/0e7b3d5f-bab0-4d45-a915-3706fd9b301a
-- title:
--   §5.2 — three-bit rank gain: at most three of the eight maps $C+\sum\varepsilon_iB_i$ have rank below $r/4$ (odd characteristic)
-- statement:
--   Let $F$ be a field of odd characteristic, $W$ a finite-dimensional $F$-vector space, $C:W\to F^d$ a linear map and $B_1,B_2,B_3:W\to F^d$ linear maps of rank at least $r$. For $\varepsilon\in\{0,1\}^3$ put $V_\varepsilon=C+\varepsilon_1B_1+\varepsilon_2B_2+\varepsilon_3B_3$. Then at most three of the eight maps $V_\varepsilon$ have rank strictly below $r/4$:
--   $$\#\{\varepsilon\in\{0,1\}^3 : \operatorname{rank}V_\varepsilon<r/4\}\le3 .$$
--   Consequently, for uniform fresh bits $\varepsilon$, the new kernel $\ker V_\varepsilon\subseteq W$ loses at least $r/4$ dimensions with probability at least $5/8$:
--   $$\frac{\#\{\varepsilon : \dim W-\dim\ker V_\varepsilon\ge r/4\}}{8}\ge\frac58 .$$
--   In the paper $W$ is the current left kernel, $B_a$ is the contribution of row $a$ to the next constraint, and $C$ collects the other fresh bits; this rank gain drives the scalar dependency bound (Lemma 5.2).
--
--   Differences from the source:
--   - generalization: W the current kernel, B_a the contributions of three rows (kernels {α : α_a = 0}) and C the contribution of the other fixed bits → W any finite-dimensional F-vector space and C, B₁, B₂, B₃ any linear maps W → F^d with rank B_i ≥ r; reason: the claim uses only the ranks; the source's maps are a special case
--   - encoding: field F of odd characteristic → Odd (ringChar F); reason: the characteristic of a field is 0 or a prime; Odd excludes 0 and 2, leaving exactly the odd primes
--   - encoding: with probability at least 5/8 over the three fresh fair bits, the kernel loses at least r/4 dimensions → #{ε ∈ {0,1}³ : dim W − dim ker V_ε ≥ r/4}/8 ≥ 5/8; reason: fresh fair bits are uniform on {0,1}³, and the next kernel is ker V_ε ⊆ W
--   - encoding: ranks compared with r/4 → Module.finrank of the range, compared in ℝ with r/4; reason: r/4 need not be an integer
-- source:
--   Lin, Sharp Second-Order Thresholds for Random Algebraic Coverage, STOC 2027 submission (manuscript sha256 9db96430…), p. 19 (PDF 20), §5.2

import Mathlib

namespace AlgCoverage.OddOrder

/-- §5.2 (three-bit rank gain), Lin, printed p. 19 / PDF 20. Over a field of odd characteristic, let
`B₁, B₂, B₃ : W → F^d` be linear maps of rank at least `r` and `C : W → F^d` any linear map. Among the
eight maps `V_ε = C + ε₁B₁ + ε₂B₂ + ε₃B₃`, `ε ∈ {0,1}³`, at most three have rank strictly below `r/4`;
consequently, for uniform fresh bits `ε`, the kernel `ker V_ε ⊆ W` has at least `r/4` fewer dimensions
than `W` with probability at least `5/8`. -/
theorem three_bit_rank_gain {F : Type*} [Field F] (hF : Odd (ringChar F))
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W] (d r : ℕ)
    (C : W →ₗ[F] (Fin d → F)) (B : Fin 3 → W →ₗ[F] (Fin d → F))
    (hB : ∀ i, r ≤ Module.finrank F (LinearMap.range (B i))) :
    Nat.card {ε : Fin 3 → Bool //
        (Module.finrank F (LinearMap.range (C + ∑ i, if ε i then B i else 0)) : ℝ) < (r : ℝ) / 4}
      ≤ 3 ∧
    (5 : ℝ) / 8 ≤
      (Nat.card {ε : Fin 3 → Bool //
          (r : ℝ) / 4 ≤ (Module.finrank F W : ℝ) -
            Module.finrank F (LinearMap.ker (C + ∑ i, if ε i then B i else 0))} : ℝ) / 8 := by sorry

end AlgCoverage.OddOrder
