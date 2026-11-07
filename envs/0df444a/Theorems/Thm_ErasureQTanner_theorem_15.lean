-- Prove2me | Theorems.Thm_ErasureQTanner_theorem_15
-- name    : ErasureQTanner.theorem_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:08:10.588766+00:00
-- url     : https://prove2.me/theorems/268a0b41-db4c-40a5-82d4-5cf39ac9a1c6
-- title:
--   Theorem 15 — duals of random tensor codes reach capacity
-- statement:
--   Fix $\rho_1,\rho_2\in(0,1)$ and $\nu\in(0,\frac13)$. There is $n_0$ such that for $n>n_0$, the dual tensor code $C:=(C_1\otimes C_2)^\perp$ of two independent uniform random linear codes of rates $1-\rho_1$, $1-\rho_2$ satisfies
--   $$\Pr_{C_1,C_2,\,x\sim1-\rho-n^{-1/2+3\nu/2}}[\mathrm{decode}(C,x)=0]\le4n^{-\nu/2}\qquad\text{for }\rho:=\rho_1+\rho_2-\rho_1\rho_2.$$
--   This is the classical result the quantum construction needs: the rate of $C$ tends to $\rho$, so $1-\rho$ is its capacity.
--
--   Differences from the source:
--   - reading: random linear codes of rates $1-\rho_i$ → every dimension $k_i$ with $|k_i-(1-\rho_i)n|\le1$; reason: an exact rate $k/n$ does not exist at an irrational $\rho_i$; the gaps of the bound are much larger than $1/n$, and every rounding is covered
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), Theorem 15, pp.22–23

import Mathlib
import Definitions.Def_QAlgorithms_Defs_TensorCode
import Definitions.Def_ErasureQTanner_noisyProb
import Definitions.Def_ErasureQTanner_covered
import Definitions.Def_ErasureQTanner_uniformAvg

set_option autoImplicit false

open QAlgorithms

namespace ErasureQTanner

/-- **Theorem 15.** Pfister, Sprumont, Zémor, *Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels*, STOC 2027 submission (manuscript sha256 bf7a84a5…), pp.22–23: fix `ρ₁, ρ₂ ∈ (0, 1)`, `ν ∈ (0, 1/3)`. There is `n₀` such that for `n > n₀`,
the dual tensor code `C := (C₁ ⊗ C₂)^⊥` of two independent uniform random linear codes of rates `1 − ρ₁`, `1 − ρ₂` satisfies
`Pr_{C₁,C₂, x∼1−ρ−n^{−1/2+3ν/2}}[decode(C, x) = 0] ≤ 4n^{−ν/2}` for `ρ := ρ₁ + ρ₂ − ρ₁ρ₂`.

**Formalization Note.** Dimensions are every `k_i` within `1` of `(1 − ρ_i)n`. The erasure rate lies in `[0, 1]` for large `n`, which
`n₀` provides. -/
theorem theorem_15 (ρ₁ ρ₂ ν : ℝ) (hρ₁ : ρ₁ ∈ Set.Ioo (0 : ℝ) 1) (hρ₂ : ρ₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hν : ν ∈ Set.Ioo (0 : ℝ) (1 / 3)) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ < n → ∀ k₁ k₂ : ℕ,
      |(k₁ : ℝ) - (1 - ρ₁) * n| ≤ 1 → |(k₂ : ℝ) - (1 - ρ₂) * n| ≤ 1 →
      uniformAvg n k₁ (fun C₁ => uniformAvg n k₂ fun C₂ =>
        noisyProb (1 - (ρ₁ + ρ₂ - ρ₁ * ρ₂) - (n : ℝ) ^ (-(1 / 2 : ℝ) + 3 * ν / 2))
          (decodeFails (codeDual (tensorCode C₁ C₂)))) ≤
        4 * (n : ℝ) ^ (-(ν / 2)) := by sorry

end ErasureQTanner
