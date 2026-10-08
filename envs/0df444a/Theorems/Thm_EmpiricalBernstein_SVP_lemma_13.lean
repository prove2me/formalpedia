-- Prove2me | Theorems.Thm_EmpiricalBernstein_SVP_lemma_13
-- name    : EmpiricalBernstein.SVP.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:15.399805+00:00
-- url     : https://prove2.me/theorems/eb3440f7-4821-4ebb-b0cb-8591509ec74d
-- title:
--   Lemma 13 — $\mathbb EF(X,X') \le \sup_{(x,x')}\mathbb E_\sigma F((\sigma,x,x'),(-\sigma,x,x'))$
-- statement:
--   Let $X = (X_1,\dots,X_n)$ and $X' = (X'_1,\dots,X'_n)$ be random vectors with values in $\mathcal X^n$ such that all the $X_i$ and $X'_i$ are independent and identically distributed with law $\mu$. Let $G : \mathcal X^{2n} \to [0,1]$. Then
--
--   $$
--   \mathbb E\, G(X, X') \le \sup_{(x,x') \in \mathcal X^{2n}} \mathbb E_\sigma\, G\big((\sigma,x,x'), (-\sigma,x,x')\big),
--   $$
--
--   where $\sigma = (\sigma_1,\dots,\sigma_n)$ has independent coordinates uniform on $\{-1,1\}$ and $(\sigma,x,x')$ is the swapped vector.
--
--   This is the symmetrization step of the double-sample method: swapping $X_i$ and $X'_i$ does not change the joint law, so the expectation can be bounded by a worst case over fixed double samples, where only the random signs remain.
--
--   **Formalization Note** The paper calls the function $F$; it is `G` here because `F` is the hypothesis class elsewhere in the mission. $(X,X')$ has law $\mu^n \otimes \mu^n$ on `(Fin n → 𝒳) × (Fin n → 𝒳)`; $\mathbb E_\sigma$ is the uniform average over the $2^n$ vectors `σ : Fin n → Bool`. **Added hypothesis**: $G$ is measurable, making precise the paper's convention that measurability questions are ignored. The supremum is a real supremum of values in $[0,1]$, hence bounded.
-- source:
--   Maurer, Pontil, Empirical Bernstein Bounds and Sample Variance Penalization, arXiv:0907.3740v1, Lemma 13, p. 5

import Mathlib
import Definitions.Def_EmpiricalBernstein_SVP_swap

open MeasureTheory

namespace EmpiricalBernstein.SVP

/-- Lemma 13 (arXiv:0907.3740v1, p. 5): `X, X′` independent i.i.d. samples of size `n` from `μ`;
`𝔼_σ` is the uniform average over the `2^n` sign vectors `σ`; `G` is the paper's `F`. -/
theorem lemma_13 {𝒳 : Type*} [MeasurableSpace 𝒳] (μ : Measure 𝒳) [IsProbabilityMeasure μ]
    {n : ℕ} (G : (Fin n → 𝒳) × (Fin n → 𝒳) → ℝ) (hGm : Measurable G)
    (hG : ∀ p, G p ∈ Set.Icc (0 : ℝ) 1) :
    ∫ p, G p ∂((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ))
      ≤ ⨆ p : (Fin n → 𝒳) × (Fin n → 𝒳),
          ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
            G (swap σ p.1 p.2, swap (fun i => !σ i) p.1 p.2) := by sorry

end EmpiricalBernstein.SVP
