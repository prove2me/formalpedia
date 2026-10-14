-- Prove2me | Theorems.Thm_CondPortOT_SingUninf_condExp_le_sup
-- name    : CondPortOT.SingUninf.condExp_le_sup
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:15.990679+00:00
-- url     : https://prove2.me/theorems/91db828e-1aa0-4f2d-b25c-eebe36552899
-- title:
--   p. 41 — E_ℚ[ℓ(Y) | (X, Y) ∈ S] ≤ sup_{y∈𝒴} ℓ(y) whenever ℚ(S) > 0
-- statement:
--   Let $\mathbb Q$ be a probability measure on $\mathcal X\times\mathcal Y$, let $S\subseteq\mathcal X\times\mathcal Y$ be measurable with $\mathbb Q(S)>0$, and let $\ell:\mathcal Y\to\mathbb R$ be any function. Then
--
--   $$\mathbb E_{\mathbb Q}[\ell(Y)\mid (X,Y)\in S]\le\sup_{y\in\mathcal Y}\ell(y),$$
--
--   both sides taken in $[-\infty,+\infty]$, where the conditional expectation is $\mathbb Q(S)^{-1}\big(\int_S\ell^+(y)\,\mathbb Q(dx\times dy)-\int_S\ell^-(y)\,\mathbb Q(dx\times dy)\big)$.
--
--   This is the upper-bound half of Proposition 3.1 (with $S$ the fiber $\{x_0\}\times\mathcal Y$): a conditional law of $Y$ is supported on $\mathcal Y$, so it cannot average $\ell$ above its supremum. It is stated for a general measurable $S$ so that it applies to every fiber $\mathcal N_\gamma(x_0)\times\mathcal Y$.
--
--   **Formalization Note** The integrals are lower Lebesgue integrals of the positive and negative parts; no measurability or integrability of $\ell$ is assumed.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, p. 41, proof of Proposition 3.1, last display

import Mathlib
import Definitions.Def_CondPortOT_SingUninf_Setting

open MeasureTheory

namespace CondPortOT.SingUninf

theorem condExp_le_sup {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (Q : Measure (X × Y)) [IsProbabilityMeasure Q] (S : Set (X × Y)) (hS : MeasurableSet S)
    (hQS : 0 < Q S) (L : Y → ℝ) :
    condExp Q S L ≤ ⨆ y, (L y : EReal) := by sorry

end CondPortOT.SingUninf
