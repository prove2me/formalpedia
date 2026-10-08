-- Prove2me | Theorems.Thm_CorreaThreshold_Nonadaptive_lemma_2
-- name    : CorreaThreshold.Nonadaptive.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:38.290308+00:00
-- url     : https://prove2.me/theorems/592c7c33-2df0-459e-9641-991fb2791c39
-- title:
--   Lemma 2, p. 1458 — equivalence between the global φ_n and h_n bounds
-- statement:
--   The bound $\varphi_n(y)\ge1-1/e$ for all integers $n\ge2$ and $y\in[0,1]$ is equivalent to nonnegativity of $h_n(x)$ for all integers $n\ge1$ and $x\in[0,1/(n-1+e/2)]$:
--
--   $$\bigl[\forall n\ge2\ \forall y\in[0,1],\ \varphi_n(y)\ge1-1/e\bigr]\ \Longleftrightarrow\ \bigl[\forall n\ge1\ \forall x\in[0,1/(n-1+e/2)],\ h_n(x)\ge0\bigr].$$
--
--   The equivalence transfers the required bound on the factor in (5) to an inequality for $h$.
--
--   **Formalization Note** The formula (6) has a removable $0/0$ at $y=1$, where $\varphi_n$ is defined by its continuous value $2/e$.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), p. 1458, Lemma 2 and (6), proof pp. 1468–1469; https://doi.org/10.1287/moor.2020.1105

import Mathlib
import Definitions.Def_CorreaThreshold_Nonadaptive_Bernoulli

namespace CorreaThreshold.Nonadaptive

/-- Lemma 2, with its two globally quantified inequalities. -/
theorem lemma_2 :
    (∀ n : ℕ, 2 ≤ n → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      1 - Real.exp (-1) ≤ phi n y) ↔
    (∀ n : ℕ, 1 ≤ n → ∀ x ∈ Set.Icc (0 : ℝ)
      (1 / ((n : ℝ) - 1 + Real.exp 1 / 2)), 0 ≤ h n x) := by sorry

end CorreaThreshold.Nonadaptive
