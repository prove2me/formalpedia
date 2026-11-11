-- Prove2me | Theorems.Thm_ContinualHardness_Linear_theorem_A_1
-- name    : ContinualHardness.Linear.theorem_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:12:04.984979+00:00
-- url     : https://prove2.me/theorems/273999d3-f9f0-4dae-8e85-4b4a258eba52
-- title:
--   Theorem A.1 — Berry–Esseen theorem for independent, non-identically distributed summands
-- statement:
--   There is an absolute constant $c_1>0$ with the following property. Let $X_1,\dots,X_n$ ($n\ge1$) be independent real random variables on a probability space with $\mathbb E[X_i]=0$, $\operatorname{Var}[X_i]=\sigma_i^2>0$ and finite third absolute moments; let $\sigma^2=\sum_{i\in[n]}\sigma_i^2$ and $\gamma=\sigma^{-1}\max_{i\in[n]}\mathbb E[|X_i|^3]/\sigma_i^2$. Then
--   $$\sup_{t\in\mathbb R}\Big|\Pr\Big[\sigma^{-1}\sum_{i\in[n]}X_i\le t\Big]-\Phi(t)\Big|\ \le\ c_1\gamma ,$$
--   with $\Phi$ the CDF of $N(0,1)$. In Lean: some $c_1$ satisfies `IsBerryEsseenConstant c₁`, which includes $c_1>0$ and the inequality for every $n$, probability space and family as above. The constant enters the dictatorship test through $\tau$ in (7).
--
--   Differences from the source:
--   - encoding: X_1, …, X_n with Var[X_i] = σ_i²; γ = σ⁻¹ max_i E[|X_i|³]/σ_i² → n ≥ 1, σ_i² > 0, E|X_i|³ < ∞ (MemLp 3) and each X_i measurable; reason: γ divides by σ_i² and takes a maximum over [n], so it is undefined otherwise; with an infinite third moment γ = ∞ and the bound is void, while a Lean integral of a non-integrable function is 0
--   - encoding: sup_{t∈ℝ} |…| ≤ c_1γ with c_1 an absolute constant → ∃ c₁, IsBerryEsseenConstant c₁: c₁ > 0 chosen before n, the probability space Ω : Type and the X_i, and the inequality for every t; reason: Lean representation; the constant is uniform as printed
-- source:
--   Saket, Intractability of Continual Learning using Parametric Models with Unlimited Replay Buffer, STOC 2027 submission (manuscript sha256 86821df1…), p. 16, Theorem A.1, Eq. (5) (PDF p. 17)

import Mathlib
import Definitions.Def_ContinualHardness_Linear_BerryEsseen

namespace ContinualHardness.Linear

/-- Theorem A.1 (Berry–Esseen Theorem), p. 16. There is an absolute constant `c₁ > 0` such that
for all independent centred random variables `X₁, …, Xₙ` with variances `σᵢ² > 0` (and finite third
absolute moments), `sup_t |Pr[σ⁻¹ ∑ᵢ Xᵢ ≤ t] − Φ(t)| ≤ c₁ γ`, where `σ² = ∑ᵢ σᵢ²` and
`γ = σ⁻¹ maxᵢ E[|Xᵢ|³]/σᵢ²`. -/
theorem theorem_A_1 : ∃ c₁ : ℝ, IsBerryEsseenConstant c₁ := by sorry

end ContinualHardness.Linear
