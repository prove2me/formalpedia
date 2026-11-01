-- Prove2me | Theorems.Thm_FisherInfoIneq_fisher_information_inequality
-- name    : FisherInfoIneq.fisher_information_inequality
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:57:31.420154+00:00
-- url     : https://prove2.me/theorems/1bea5f43-aafa-40f2-b7a7-97e64ba3ac72
-- title:
--   Eq. (4) — the Fisher information inequality $(a+b)^2J(N_1+N_2)\le a^2J(N_1)+b^2J(N_2)$
-- statement:
--   Let $N_1$ and $N_2$ be independent real random variables with probability density functions, on a probability space $(\Omega,P)$. Then for all $a,b\ge0$,
--   $$(a+b)^2\,J(N_1+N_2)\le a^2\,J(N_1)+b^2\,J(N_2),$$
--   where $J(X)=\mathbb E[\rho_X(X)^2]=\int f'^2/f$ is the Fisher information of $X$ (with respect to a translation parameter), $f$ the density of $X$ and $\rho_X=f'/f$ its score.
--
--   This is the classical Fisher information inequality of Stam (1959) and Blachman (1965). Choosing $a=1/J(N_1)$, $b=1/J(N_2)$ gives the canonical form $1/J(N_1+N_2)\ge1/J(N_1)+1/J(N_2)$, the Fisher-information counterpart of the entropy power inequality.
--
--   **Formalization Note** $J$ takes values in $[0,\infty]$, with $J=+\infty$ for a law without an absolutely continuous density; no finiteness of $J(N_1)$, $J(N_2)$ is assumed. The coefficients are nonnegative reals and $0\cdot\infty=0$.
--
--   Differences from the source:
--   - encoding: J(X) = COV{ρ_X(X)} for X with a density f, ρ_X = f′/f → fisherInfo (P.map X) = ∫ f′²/f ∈ [0, ∞] over an absolutely continuous density f, and +∞ when the law has none; reason: J is valued in [0, ∞] so that infinite Fisher information is representable; every law with an absolutely continuous density gets the classical value, and +∞ otherwise is the standard convention under which the inequality is stated for all densities
--   - reading: COV{ρ_X(X)} → E[ρ_X(X)²]; reason: the score has mean zero (eq. (30), p.5: 'score functions always have zero mean'), so the variance equals the second moment; the paper itself uses J(X) = E[ρ_X²(X)] in (30)
--   - encoding: real coefficients (a + b)², a², b² multiplying J → ENNReal.ofReal ((a + b)²), ENNReal.ofReal (a²), ENNReal.ofReal (b²) in [0, ∞], with 0 · ∞ = 0; reason: J may be +∞ and the page has no finiteness hypothesis; for finite J it is the same inequality, and 0 · ∞ = 0 is the measure-theoretic convention that makes a = 0 or b = 0 read as the inequality without that term
-- source:
--   Liu–Viswanath, Two Proofs of the Fisher Information Inequality via Data Processing Arguments, arXiv:cs/0604028v1, eq. (4), p.2; proved in §2.2, pp.4–5 ('The desired inequality (4) thus follows from (29) by letting t ↓ 0', p.5)

import Mathlib
import Definitions.Def_FisherInfoIneq_fisherInfo

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FisherInfoIneq

/-- **Display (4): the classical Fisher information inequality.** Let `N₁` and `N₂` be two
independent real random variables with probability density functions on a probability space
`(Ω, P)`. Then for all `a, b ≥ 0`,
`(a + b)² J(N₁ + N₂) ≤ a² J(N₁) + b² J(N₂)`.

Liu–Viswanath, *Two Proofs of the Fisher Information Inequality via Data Processing Arguments*,
arXiv:cs/0604028v1, eq. (4), p.2. Proved in §2.2 (pp.4–5): "The desired inequality (4) thus
follows from (29) by letting t ↓ 0."

**Formalization Note**
1. `J(X) = fisherInfo (P.map X) = ∫ f′²/f ∈ [0, ∞]` (eq. (2) read as `E[ρ_X(X)²]`, eq. (30)), with
   `J = +∞` for a law without an absolutely continuous density.
2. No finiteness of `J(N₁)`, `J(N₂)` is assumed; the coefficients are `ENNReal.ofReal` of the real
   squares, and `0 · ∞ = 0` in `ℝ≥0∞` (so `a = 0` with `J(N₁) = ∞` reads `b² J(N₁+N₂) ≤ b² J(N₂)`).
3. "Probability density functions" is `HasPDF` with respect to Lebesgue measure. -/
theorem fisher_information_inequality {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (N₁ N₂ : Ω → ℝ) (hN₁ : Measurable N₁) (hN₂ : Measurable N₂) (hind : IndepFun N₁ N₂ P) (hpdf₁ : HasPDF N₁ P) (hpdf₂ : HasPDF N₂ P) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : ENNReal.ofReal ((a + b) ^ 2) * fisherInfo (P.map (N₁ + N₂)) ≤ ENNReal.ofReal (a ^ 2) * fisherInfo (P.map N₁) + ENNReal.ofReal (b ^ 2) * fisherInfo (P.map N₂) := by sorry

end FisherInfoIneq
