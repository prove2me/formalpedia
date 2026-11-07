-- Prove2me | Theorems.Thm_ErasureQTanner_theorem_12
-- name    : ErasureQTanner.theorem_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:07:13.710359+00:00
-- url     : https://prove2.me/theorems/fd1b35ac-da26-4d24-8643-e0f583050921
-- title:
--   Theorem 12 — random dual tensor codes are product expanding
-- statement:
--   Let $\rho_1,\rho_2\in(0,1)$, $n>8/\min\{\rho_1,\rho_2\}$, and let $C_1,C_2\subseteq\mathbb F_2^n$ be random linear codes of dimensions $\rho_1n$, $\rho_2n$. With
--   $$\kappa:=\frac12\min\Big\{\frac14h^{-1}\big(\frac{\rho_1}8\big)h^{-1}\big(\frac{\rho_2}8\big),h^{-1}\big(\frac{\rho_1\rho_2}8\big)\Big\},$$
--   $$\Pr_{C_1,C_2}\big[(C_1\otimes C_2)^\perp\text{ is }\kappa\text{-expanding}\big]\ge1-\varepsilon,\qquad\varepsilon=5\cdot2^{-\frac{\rho_1\rho_2}8n^2}+16\cdot2^{-\frac{\rho_1\rho_2}8n}.$$
--   A code $(C_1\otimes C_2)^\perp$ is $\kappa$-expanding when each word $c$ decomposes as $c_{\mathrm{col}}+c_{\mathrm{row}}$, columns in $C_1^\perp$, rows in $C_2^\perp$, with $\mathrm{wt}(c)\ge\kappa n(\|c_{\mathrm{col}}\|+\|c_{\mathrm{row}}\|)$. This result of Kalachev and Panteleev is cited; it powers Lemma 14.
--
--   Differences from the source:
--   - encoding: dimensions $\rho_in$, with $\rho_i\in(0,1)$ → dimensions $k_i$ with $0<k_i<n$, $\rho_i:=k_i/n$; reason: these are the cases where $\rho_in$ is an integer dimension
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), Theorem 12, p.20

import Mathlib
import Definitions.Def_QAlgorithms_Defs_TensorCode
import Definitions.Def_ErasureQTanner_uniformAvg
import Definitions.Def_ErasureQTanner_kp22Kappa

set_option autoImplicit false

open QAlgorithms

namespace ErasureQTanner

/-- **Theorem 12** ([KP22]). Pfister, Sprumont, Zémor, *Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels*, STOC 2027 submission (manuscript sha256 bf7a84a5…), p.20: for `ρ₁, ρ₂ ∈ (0, 1)`, `n > 8/min{ρ₁, ρ₂}` and random linear
`C₁, C₂ ⊆ F₂ⁿ` of dimensions `ρ₁n`, `ρ₂n`, with `κ := (1/2)min{(1/4)h⁻¹(ρ₁/8)h⁻¹(ρ₂/8), h⁻¹(ρ₁ρ₂/8)}`,
`Pr[(C₁ ⊗ C₂)^⊥ is κ-expanding] ≥ 1 − ε` for `ε = 5·2^{−(ρ₁ρ₂/8)n²} + 16·2^{−(ρ₁ρ₂/8)n}`.

**Formalization Note.** `ρ_i := k_i/n` with `0 < k_i < n`. "`(C₁ ⊗ C₂)^⊥` is `κ`-expanding" (p.20: columns in `C₁^⊥`, rows in
`C₂^⊥`) is `IsProductExpanding (codeDual C₁) (codeDual C₂) n κ`, whose domain `dualTensorCode` is `(C₁ ⊗ C₂)^⊥`. The two codes
are independent: the probability is the average over `C₁` of the probability over `C₂`. -/
theorem theorem_12 (n k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₁n : k₁ < n) (hk₂ : 0 < k₂) (hk₂n : k₂ < n)
    (hn : 8 / min ((k₁ : ℝ) / n) ((k₂ : ℝ) / n) < n) :
    1 - (5 * (2 : ℝ) ^ (-(((k₁ : ℝ) / n) * ((k₂ : ℝ) / n) / 8 * (n : ℝ) ^ 2)) +
          16 * (2 : ℝ) ^ (-(((k₁ : ℝ) / n) * ((k₂ : ℝ) / n) / 8 * (n : ℝ)))) ≤
      uniformAvg n k₁ (fun C₁ => uniformProb n k₂ fun C₂ =>
        IsProductExpanding (codeDual C₁) (codeDual C₂) n (kp22Kappa ((k₁ : ℝ) / n) ((k₂ : ℝ) / n))) := by sorry

end ErasureQTanner
