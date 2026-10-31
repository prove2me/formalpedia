-- Prove2me | Theorems.Thm_DistortedCondExp_proposition_2_5_i
-- name    : DistortedCondExp.proposition_2_5_i
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:58:50.128319+00:00
-- url     : https://prove2.me/theorems/edb55bf0-dbb1-4a47-8d43-1ded5215057f
-- title:
--   Proposition 2.5(i): the distorted expectation of a finitely valued random variable
-- statement:
--   Let $\varphi$ be a distortion function and $(\Omega,\mathcal F,\mathbb P)$ a probability space.
--
--   1. **(2.2)** If $\eta\ge0$ takes only finitely many values $x_1,\dots,x_n$, then
--   $$
--   \mathcal E[\eta]=\sum_{k=1}^n x_{(k)}\Bigl[\varphi\bigl(\mathbb P(\eta\ge x_{(k)})\bigr)-\varphi\bigl(\mathbb P(\eta\ge x_{(k+1)})\bigr)\Bigr],
--   $$
--   where $x_{(1)}\le\dots\le x_{(n)}$ are the ordered values of $x_1,\dots,x_n$ and $x_{(n+1)}:=\infty$.
--   2. **(2.3)** If $x_1<\dots<x_n$, $\eta$ takes values among them, and $g\in\mathcal I$, then
--   $$
--   \mathcal E[g(\eta)]=\sum_{k=1}^n g(x_k)\bigl[\varphi(\mathbb P(\eta\ge x_k))-\varphi(\mathbb P(\eta\ge x_{k+1}))\bigr].
--   $$
--
--   Formula (2.3) says that, for a fixed finitely valued $\eta$, $\mathcal E[g(\eta)]$ is the ordinary expectation of $g(\eta)$ under the distorted point masses $\varphi(\mathbb P(\eta\ge x_k))-\varphi(\mathbb P(\eta\ge x_{k+1}))$, the same for every $g\in\mathcal I$. It is the computation behind every identity on the binomial tree.
--
--   **Formalization Note** Indices are 0-based; the ordered values are $x\circ\sigma$ for the sorting permutation `Tuple.sort`. The term with $x_{(n+1)}=\infty$ is written $\varphi(0)$ $(=\varphi(\mathbb P(\eta\ge\infty)))$. A finitely valued $\eta\ge0$ automatically has $\mathcal E[\eta]<\infty$.
--
--   Differences from the source:
--   - generalization: (2.3) for η ∈ 𝕃¹_φ(F), i.e. η ≥ 0 → (2.3) for every measurable real-valued η whose values lie among x_1 < ⋯ < x_n; reason: the proof of Theorem 3.4 applies (2.3) to η = X_{t_n}, whose nodes may be negative; the formula holds because g ≥ 0, and it specializes to η ≥ 0
--   - generalization: η takes only finitely many values x_1, …, x_n → every value of η is one of x_1, …, x_n (a listed value need not be attained); reason: an unattained value contributes a zero term; when every x_k is attained this is the page's hypothesis
--   - encoding: η ∈ 𝕃¹_φ(F), x_(n+1) := ∞, indices 1, …, n → measurable η ≥ 0 (then 𝓔[η] < ∞ automatically), the last term φ(0), indices Fin n, ordered values xv ∘ Tuple.sort xv; reason: the same quantities; φ(ℙ(η ≥ ∞)) = φ(0)
--   - encoding: ∫₀^∞ φ(P(ξ ≥ x)) dx → Bochner integral over (0, ∞); reason: finite for finitely valued ξ, where it equals the paper's integral
-- source:
--   Ma–Wong–Zhang, Time-consistent conditional expectation under probability distortion, arXiv:1809.08262v5, https://arxiv.org/abs/1809.08262v5, Proposition 2.5(i), eqs. (2.2)–(2.3), p.5

import Mathlib
import Definitions.Def_DistortedCondExp_Distortion

open MeasureTheory Set

namespace DistortedCondExp

/-- **Proposition 2.5(i)** (Ma–Wong–Zhang, *Time-consistent conditional expectation under
probability distortion*, arXiv:1809.08262v5, eqs. (2.2) and (2.3), p.5). Let `φ` be a distortion
function on a probability space `(Ω, F, P)`.

1. (2.2) If `η ≥ 0` takes only finitely many values `x_1, …, x_n`, then
   `𝓔[η] = ∑_{k=1}^n x_(k) [φ(P(η ≥ x_(k))) − φ(P(η ≥ x_(k+1)))]`, where
   `x_(1) ≤ ⋯ ≤ x_(n)` are the ordered values and `x_(n+1) := ∞`.
2. (2.3) If `x_1 < ⋯ < x_n` and `g ∈ ℐ`, then
   `𝓔[g(η)] = ∑_{k=1}^n g(x_k) [φ(P(η ≥ x_k)) − φ(P(η ≥ x_{k+1}))]`.

**Formalization Note** Indices are `Fin n` (0-based). The ordered values are `xv ∘ Tuple.sort xv`.
The term with `x_(n+1) := ∞` is `φ(P(η ≥ ∞)) = φ(0)`. "Takes only finitely many values
`x_1, …, x_n`" is the hypothesis that every value of `η` is one of them (a listed value need not be
attained). Such an `η ≥ 0` is automatically in `𝕃¹_φ`. Clause 2 is stated for real-valued
measurable `η` (the paper takes `η ∈ 𝕃¹_φ(F)`, `η ≥ 0`); the proof of Theorem 3.4 applies (2.3) to
`η = X_{t_n}`, whose values may be negative. -/
theorem proposition_2_5_i {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (φ : ℝ → ℝ) (hφ : IsDistortion φ) :
    (∀ (n : ℕ) (xv : Fin n → ℝ) (η : Ω → ℝ), Measurable η → (∀ ω, 0 ≤ η ω) →
      (∀ ω, ∃ k, η ω = xv k) →
      distortedExp μ φ η =
        ∑ k : Fin n, (xv ∘ Tuple.sort xv) k *
          (φ (μ.real {ω | (xv ∘ Tuple.sort xv) k ≤ η ω}) -
            (if h : (k : ℕ) + 1 < n then
              φ (μ.real {ω | (xv ∘ Tuple.sort xv) ⟨(k : ℕ) + 1, h⟩ ≤ η ω})
            else φ 0))) ∧
    (∀ (n : ℕ) (xv : Fin n → ℝ) (η : Ω → ℝ) (g : ℝ → ℝ), StrictMono xv → InI g →
      Measurable η → (∀ ω, ∃ k, η ω = xv k) →
      distortedExp μ φ (fun ω => g (η ω)) =
        ∑ k : Fin n, g (xv k) *
          (φ (μ.real {ω | xv k ≤ η ω}) -
            (if h : (k : ℕ) + 1 < n then φ (μ.real {ω | xv ⟨(k : ℕ) + 1, h⟩ ≤ η ω})
            else φ 0))) := by sorry

end DistortedCondExp
