-- Prove2me | Theorems.Thm_ErasureQTanner_lemma_14
-- name    : ErasureQTanner.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:07:30.831224+00:00
-- url     : https://prove2.me/theorems/dd46eb8d-7e91-406a-88ef-bf7ca806126a
-- title:
--   Lemma 14 — covered words of the dual tensor code are heavy
-- statement:
--   Fix $\tau\in(0,2)$, $\rho_1,\rho_2\in(0,1)$. There are $n_0$ and $a>0$, depending only on these, such that for $n>n_0$ the dual tensor code $C:=(C_1\otimes C_2)^\perp$ of two random linear codes of rates $1-\rho_1$, $1-\rho_2$ satisfies, for $\rho:=1-\rho_1-\rho_2+\rho_1\rho_2$,
--   $$\Pr_{C_1,C_2,\,x\sim\rho}\big[\exists c\in S_C(x):0<\mathrm{wt}(c)\le n^{2-\tau}\big]\le e^{-an}.$$
--   So at capacity, the covered words are almost certainly of weight close to $n^2$. Theorem 15's proof uses this to bound the probability of covering a light word.
--
--   Differences from the source:
--   - generalization: $\exists c\in S_C(x):\mathrm{wt}(c)=n^{2-\tau}$ → $\exists c\in S_C(x):0<\mathrm{wt}(c)\le n^{2-\tau}$; reason: the printed event is contained in this one since $n^{2-\tau}>0$, so this implies the printed lemma; eq. (19) unions over at most $n^2$ weights, which needs this form because $n_0$, $a$ depend on the fixed $\tau$
--   - reading: random linear codes of rates $1-\rho_i$ → every dimension $k_i$ with $|k_i-(1-\rho_i)n|\le1$; reason: an exact rate $k/n$ does not exist at an irrational $\rho_i$; the gaps of the bound are much larger than $1/n$, and every rounding is covered
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), Lemma 14, p.21

import Mathlib
import Definitions.Def_QAlgorithms_Defs_TensorCode
import Definitions.Def_ErasureQTanner_noisyProb
import Definitions.Def_ErasureQTanner_covered
import Definitions.Def_ErasureQTanner_uniformAvg

set_option autoImplicit false

open QAlgorithms

namespace ErasureQTanner

/-- **Lemma 14.** Pfister, Sprumont, Zémor, *Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels*, STOC 2027 submission (manuscript sha256 bf7a84a5…), p.21: fix `τ ∈ (0, 2)`, `ρ₁, ρ₂ ∈ (0, 1)`. There is `n₀` such that for `n > n₀`, the dual
tensor code `C := (C₁ ⊗ C₂)^⊥` of two random linear codes of rates `1 − ρ₁`, `1 − ρ₂` satisfies, for
`ρ := 1 − ρ₁ − ρ₂ + ρ₁ρ₂`, `Pr[∃c ∈ S_C(x) : wt(c) = n^{2−τ}] ≤ e^{−an}`, with `a = a(τ, ρ₁, ρ₂) > 0`.

**Formalization Note.** The event is widened to `0 < wt(c) ≤ n^{2−τ}`: it contains the printed one, and the union in (19) over
"at most `n²` possible weights" needs it, since the printed `n₀` and `a` depend on the fixed `τ`. Dimensions are every `k_i`
within `1` of `(1 − ρ_i)n`: an exact rate is impossible at irrational `ρ_i`. -/
theorem lemma_14 (τ ρ₁ ρ₂ : ℝ) (hτ : τ ∈ Set.Ioo (0 : ℝ) 2) (hρ₁ : ρ₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hρ₂ : ρ₂ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ (n₀ : ℕ) (a : ℝ), 0 < a ∧ ∀ n : ℕ, n₀ < n → ∀ k₁ k₂ : ℕ,
      |(k₁ : ℝ) - (1 - ρ₁) * n| ≤ 1 → |(k₂ : ℝ) - (1 - ρ₂) * n| ≤ 1 →
      uniformAvg n k₁ (fun C₁ => uniformAvg n k₂ fun C₂ =>
        noisyProb (1 - ρ₁ - ρ₂ + ρ₁ * ρ₂) fun x =>
          ∃ c ∈ covered (codeDual (tensorCode C₁ C₂)) x, c ≠ 0 ∧
            (hammingNorm c : ℝ) ≤ (n : ℝ) ^ (2 - τ)) ≤
        Real.exp (-(a * n)) := by sorry

end ErasureQTanner
