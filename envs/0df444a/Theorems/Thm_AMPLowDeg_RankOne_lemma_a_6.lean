-- Prove2me | Theorems.Thm_AMPLowDeg_RankOne_lemma_a_6
-- name    : AMPLowDeg.RankOne.lemma_a_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:06:05.700839+00:00
-- url     : https://prove2.me/theorems/6a075ce2-e9d4-4155-bbe1-728709d61451
-- title:
--   Lemma A.6 — regularity of the scalar posterior
-- statement:
--   Let $\pi$ be any probability measure on $\mathbb R$ and let $\pi_{s,h}$ be the scalar posterior (4.1).
--
--   1. For $0<s_0<s_1<\infty$ and every integer $r\ge1$ there is a constant $C=C(r,s_0,s_1,\pi)$ with
--   $$
--   \int|x|^r\,\pi_{s,h}(dx)\le C(1+|h|)^r,\qquad s\in[s_0,s_1],\ h\in\mathbb R.
--   $$
--   2. Every posterior moment $(s,h)\mapsto\int x^k\,\pi_{s,h}(dx)$, $k\ge0$, is infinitely differentiable on $(0,\infty)\times\mathbb R$, and each of its mixed derivatives of order $j$ in $(s,h)$ has at most polynomial growth in $h$, uniformly for $s$ in each compact interval $[s_0,s_1]\subset(0,\infty)$: there are $C$ and $L$ with absolute value at most $C(1+|h|)^L$.
--   3. The same holds for every posterior cumulant $(s,h)\mapsto\mathrm{Cum}(\Theta,\dots,\Theta)$ ($k\ge1$ copies, under $\pi_{s,h}$).
--   4. For every $n\ge1$ and $\alpha$, the graph cumulant $h\mapsto C_\alpha(h)$ of (4.3) is infinitely differentiable on $\mathbb R^n$ for each $s>0$, and each of its field derivatives of order $j$ is bounded by $C(1+\|h\|)^L$ uniformly for $s\in[s_0,s_1]$.
--
--   The constants may depend on the prior, the interval, the orders and the graph. These estimates justify every differentiation in $h$ and $s$ and every Gaussian integration by parts in the proof, for priors with unbounded support.
--
--   Differences from the source:
--
--   - encoding: every fixed mixed derivative … has at most polynomial growth in h, locally uniformly for s > 0; the same for C_α(h) and field derivatives → smoothness (ContDiffOn ∞ on (0,∞) × ℝ, ContDiff ∞ in h) plus, for each derivative order j and each [s₀, s₁] ⊂ (0, ∞), ∃ C L with ‖iteratedFDeriv j‖ ≤ C(1 + |h|)^L; reason: the norm of the j-th Fréchet derivative bounds every mixed partial of order j and is bounded by a constant times their maximum, so this is the source's sentence with its quantifiers written out
--   - encoding: ∫ |x|^r π_{s,h}(dx) ≤ C(1 + |h|)^r → the same with a lower Lebesgue integral in [0, ∞]; reason: asserts the finiteness of the integral, so no integrability convention is involved
--   - encoding: vertex 1 of [n] → the vertex ⟨0, hn⟩ : Fin n, with the hypothesis 0 < n (vertices are 0-based); reason: the paper's vertex 1 exists only for n ≥ 1; relabelling changes no instance
-- source:
--   Zhangsong Li, Almost Sharp Equivalence between Approximate Message Passing and Low-Degree Polynomials, STOC 2027 submission #180 (October 2026), source.pdf SHA-256 9eb368625386c835173a663de76761a4514eda91fb4398b726b5affa824b5a0c, p. 23, Lemma A.6 (§A.3); proof pp. 23–24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/180.pdf

import Mathlib
import Definitions.Def_AMPLowDeg_RankOne_Model
import Definitions.Def_AMPLowDeg_RankOne_Cumulant
import Definitions.Def_AMPLowDeg_RankOne_Potential
import Definitions.Def_AMPLowDeg_RankOne_Aux

open MeasureTheory ProbabilityTheory
open scoped ContDiff

namespace AMPLowDeg.RankOne

/-- Lemma A.6, p. 23 — regularity of the scalar posterior, for every prior `π`:
(i) for `0 < s₀ < s₁` and every integer `r ≥ 1` there is `C` with
`∫ |x|^r π_{s,h}(dx) ≤ C (1 + |h|)^r` for `s ∈ [s₀, s₁]`, `h ∈ ℝ`;
(ii) every posterior moment `(s, h) ↦ ∫ x^k π_{s,h}(dx)` and every posterior cumulant of order
`k ≥ 1` is smooth on `(0, ∞) × ℝ`, and each fixed mixed derivative in `(s, h)` has polynomial
growth in `h`, uniformly for `s` in compact subintervals of `(0, ∞)`;
(iii) the same holds for the graph cumulants `C_α(h)` of (4.3) and their field derivatives. -/
theorem lemma_a_6 (π : Measure ℝ) [IsProbabilityMeasure π] :
    (∀ s₀ s₁ : ℝ, 0 < s₀ → s₀ < s₁ → ∀ r : ℕ, 1 ≤ r → ∃ C : ℝ, ∀ s ∈ Set.Icc s₀ s₁, ∀ h : ℝ,
        ∫⁻ x, ENNReal.ofReal (|x| ^ r) ∂(post π s h) ≤ ENNReal.ofReal (C * (1 + |h|) ^ r)) ∧
    (∀ k : ℕ,
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => ∫ x, x ^ k ∂(post π p.1 p.2)) (Set.Ioi 0 ×ˢ Set.univ) ∧
      ∀ j : ℕ, ∀ s₀ s₁ : ℝ, 0 < s₀ → s₀ < s₁ → ∃ C : ℝ, ∃ L : ℕ,
        ∀ s ∈ Set.Icc s₀ s₁, ∀ h : ℝ,
          ‖iteratedFDeriv ℝ j (fun p : ℝ × ℝ => ∫ x, x ^ k ∂(post π p.1 p.2)) (s, h)‖ ≤
            C * (1 + |h|) ^ L) ∧
    (∀ k : ℕ, 1 ≤ k →
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => cum (post π p.1 p.2) (fun _ : Fin k => fun x : ℝ => x))
        (Set.Ioi 0 ×ˢ Set.univ) ∧
      ∀ j : ℕ, ∀ s₀ s₁ : ℝ, 0 < s₀ → s₀ < s₁ → ∃ C : ℝ, ∃ L : ℕ,
        ∀ s ∈ Set.Icc s₀ s₁, ∀ h : ℝ,
          ‖iteratedFDeriv ℝ j
              (fun p : ℝ × ℝ => cum (post π p.1 p.2) (fun _ : Fin k => fun x : ℝ => x)) (s, h)‖ ≤
            C * (1 + |h|) ^ L) ∧
    (∀ (n : ℕ) (hn : 0 < n) (α : Edge n → ℕ),
      (∀ s : ℝ, 0 < s → ContDiff ℝ ∞ (Ccum π s ⟨0, hn⟩ α)) ∧
      ∀ j : ℕ, ∀ s₀ s₁ : ℝ, 0 < s₀ → s₀ < s₁ → ∃ C : ℝ, ∃ L : ℕ,
        ∀ s ∈ Set.Icc s₀ s₁, ∀ h : Fin n → ℝ,
          ‖iteratedFDeriv ℝ j (Ccum π s ⟨0, hn⟩ α) h‖ ≤ C * (1 + ‖h‖) ^ L) := by sorry

end AMPLowDeg.RankOne
