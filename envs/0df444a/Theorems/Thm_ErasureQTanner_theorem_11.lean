-- Prove2me | Theorems.Thm_ErasureQTanner_theorem_11
-- name    : ErasureQTanner.theorem_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:07:24.855225+00:00
-- url     : https://prove2.me/theorems/f1b50eac-64cd-4d57-b3e6-1d393027207b
-- title:
--   Theorem 11 — sharp threshold of the erasure failure probability
-- statement:
--   There is a universal $a>0$ such that for every $n$ and every linear $C\subseteq\mathbb F_2^n$: if $p^*\in(0,1)$ satisfies $\Pr_{x\sim p^*}[\mathrm{decode}(C,x)=0]=\frac12$, then for all $p<p^*$,
--   $$\Pr_{x\sim p}[\mathrm{decode}(C,x)=0]\le e^{-a(p^*-p)^2d_{\min}(C)}.$$
--   It is the Tillich–Zémor sharp threshold, and the step from a failure probability of $\frac12$ to an exponentially small one in the proof of Theorem 16.
--
--   Differences from the source:
--   - encoding: $p<p^*$ → $0\le p<p^*$; reason: $p$ is an erasure probability
--   - encoding: $d_{\min}(C)$ → the value of `minDistCode C` in $\mathbb N$; reason: the hypothesis forces $C\ne0$, so the distance is finite
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), Theorem 11, p.20

import Mathlib
import Definitions.Def_QAlgorithms_Defs_TensorCode
import Definitions.Def_ErasureQTanner_noisyProb
import Definitions.Def_ErasureQTanner_covered

set_option autoImplicit false

namespace ErasureQTanner

/-- **Theorem 11** ([TZ00]). Pfister, Sprumont, Zémor, *Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels*, STOC 2027 submission (manuscript sha256 bf7a84a5…), p.20: there is a universal `a > 0` such that for every `n` and every linear
`C ⊆ F₂ⁿ`, if `p* ∈ (0, 1)` has `Pr_{x∼p*}[decode(C, x) = 0] = 1/2` then for every `p < p*`,
`Pr_{x∼p}[decode(C, x) = 0] ≤ e^{−a(p*−p)²d_min(C)}`.

**Formalization Note.** `p` is a probability, so `p ∈ [0, p*)`. A failure probability `1/2` forces `C ≠ 0`, so
`QAlgorithms.minDistCode C` is finite and `.toNat` is its value. -/
theorem theorem_11 : ∃ a : ℝ, 0 < a ∧ ∀ (n : ℕ) (C : Submodule (ZMod 2) (Fin n → ZMod 2)) (pstar : ℝ),
    pstar ∈ Set.Ioo (0 : ℝ) 1 → noisyProb pstar (decodeFails C) = 1 / 2 →
    ∀ p : ℝ, 0 ≤ p → p < pstar →
      noisyProb p (decodeFails C) ≤
        Real.exp (-(a * (pstar - p) ^ 2 * ((QAlgorithms.minDistCode C).toNat : ℝ))) := by sorry

end ErasureQTanner
