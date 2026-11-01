-- Prove2me | Theorems.Thm_ExploreLQMFG_lemma_2_10
-- name    : ExploreLQMFG.lemma_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:13:36.968093+00:00
-- url     : https://prove2.me/theorems/60259894-8374-4075-ad8e-435de66c99ae
-- title:
--   Lemma 2.10, p.24 — $|h_t|\le C_2$ and $|h^n_t|\le C_2$ almost surely
-- statement:
--   Fix $d\ge1$, $T>0$ and bounds $L_f,L_g$. There is a constant $C_2>0$ such that for all $Q,R$, all bounded Lipschitz $f,g$ with $\|Q^\dagger f\|_{1,\infty}\le L_f$, $\|R^\dagger g\|_{1,\infty}\le L_g$, all $\varepsilon\in(0,1]$, $\varpi\in(1,\sqrt2]$, every complete probability space with a $d$-dimensional Brownian motion, the Riccati solution $\eta$, every $m_0\in\mathbb R^d$, the forward solution $m$, every solution $(\bar m^n,h^n,k^n)$ of the scheme (2.10) and every bounded solution $(h^\varpi,k^\varpi)$ of (2.11), with $h=\varpi h^\varpi$: almost surely,
--   $$|h_t|\le C_2,\qquad |h^n_t|\le C_2,\qquad t\in[0,T],\ n\ge1.$$
--
--   The bound does not depend on $\varepsilon$, $\varpi$, the initial processes $\bar m^0,h^0$, or $Q,R$ beyond the two norms; it keeps the tilts $\mathbb P^{\varpi h^n/\varepsilon}$ uniformly controlled along the iteration.
--
--   Differences from the source:
--   - encoding: h = ϖh^ϖ, the intercept of (2.15)–(2.16), defined through the bounded solution of (2.11) → h := ϖ • h^ϖ for an arbitrary solution (h^ϖ, k^ϖ) of the backward equation of (2.11) in the bounded class; reason: the change of variable (2.17); the bounded solution is unique (p.22)
--   - reading: the solution classes are left implicit: hⁿ⁺¹ ∈ S^d(𝔽^W) (Lemma 2.1(ii)), kⁿ⁺¹ progressive; (2.11) solved 'in the class of bounded processes' (p.22) → scheme: m̄ⁿ, hⁿ adapted with continuous paths, (hⁿ⁺¹, kⁿ⁺¹) in L²_𝔽 (Peng1990.SMP.SolvesBSDE); limit: h^ϖ continuous with a deterministic a.s. bound, k^ϖ bounded dt⊗dℙ-a.e.; reason: the standard BSDE class for the scheme and the class in which p.22 asserts uniqueness for the limit
--   - reading: 'The two initial processes m⁰ and h⁰ are two 𝔽^W-adapted continuous processes' (p.19), with the tilted measure ℙ^{ϖh⁰/ε} used as a probability measure → m̄⁰ any adapted process with continuous paths; h⁰ any adapted process with continuous paths and a deterministic almost-sure bound on [0, T]; reason: boundedness is what makes ℙ^{ϖh⁰/ε} a probability measure (Novikov); it contains the paper's choice h⁰ = 0, and the constants do not depend on the bound
--   - encoding: time t ∈ [0, T], processes indexed by [0, T] → processes indexed by ℝ≥0, [0, T] cut out by t ≤ T; time integrals over [0, t] ⊂ ℝ; reason: Lean convention of the published Peng1990.SMP stochastic-calculus definitions; values after T never enter
--   - encoding: ℝᵈ with the Euclidean norm |·|; |·| on d × d matrices unnamed → Fin d → ℝ with |x|² = Σᵢ xᵢ² written explicitly; matrices carry the Frobenius norm; reason: Mathlib's default norm on Fin d → ℝ is the sup norm; all matrix norms are equivalent up to a factor depending only on d, which the constants absorb
--   - encoding: a constant depending only on d, T, ‖Q†f‖_{1,∞} and ‖R†g‖_{1,∞} → for every d ≥ 1, T > 0 and bounds L_f, L_g there is a constant valid for all Q, R, f, g with ‖Q†f‖_{1,∞} ≤ L_f and ‖R†g‖_{1,∞} ≤ L_g, all ε, ϖ and all data; reason: the uniform form of 'depends only on'; it is at least as strong as a function of the exact norms
--   - encoding: m₀ = 𝔼(X₀), with X₀, the idiosyncratic noise B and its intensity σ in the model → an arbitrary vector m₀ ∈ ℝᵈ; X₀, B and σ are not part of the data; reason: only 𝔼(X₀) enters (2.9)–(2.13); every m₀ ∈ ℝᵈ is 𝔼(X₀) for X₀ ≡ m₀
--   - encoding: the augmented filtration 𝔽^W of W on a complete probability space → augFiltration: the natural filtration of W (published Peng1990.SMP.brownianFiltration) joined with the σ-algebra of P-null sets, with P.IsComplete assumed; reason: on a complete space this is the usual augmentation
-- source:
--   Delarue & Vasileiadis, Exploration Noise for Learning Linear-Quadratic Mean Field Games, arXiv:2107.00839v2 (https://arxiv.org/abs/2107.00839v2), Lemma 2.10, p.24

import Mathlib
import Definitions.Def_ExploreLQMFG_Scheme

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Matrix

universe u

namespace ExploreLQMFG

/-- **Lemma 2.10** (Delarue & Vasileiadis, arXiv:2107.00839v2, p.24): there exists a constant
`C₂ > 0`, only depending on `d`, `T`, `‖Q†f‖_{1,∞}` and `‖R†g‖_{1,∞}`, such that, `ℙ` almost
surely, `|h_t| ≤ C₂` and `|hⁿ_t| ≤ C₂` for `t ∈ [0, T]`, `n ≥ 1`.

Here `h = ϖh^ϖ` is the intercept of (2.15)–(2.16), for `(h^ϖ, k^ϖ)` any bounded solution of the
backward equation of (2.11) (the change of variable (2.17)), and `hⁿ` is the scheme (2.10) for
any initial `m̄⁰` (adapted, continuous) and `h⁰` (adapted, continuous, bounded).

**Formalization Note.** "Only depending on `d, T` and the norms" is encoded as `∃ C₂` after
`d, T` and bounds `L_f, L_g` on the norms, before everything else (`Q, R, f, g, ε, ϖ`, the
probability space, `m₀`, `m̄⁰`, `h⁰` and the solutions). "Almost surely" precedes the
quantifiers over `t` and `n`. -/
theorem lemma_2_10 {d : ℕ} (hd : 0 < d) (T : ℝ≥0) (hT : 0 < T) (Lf Lg : ℝ) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (Q R : Matrix (Fin d) (Fin d) ℝ) (f g : (Fin d → ℝ) → (Fin d → ℝ)),
      IsBddLip f → IsBddLip g → oneInfNorm (tmul Q f) ≤ Lf → oneInfNorm (tmul R g) ≤ Lg →
      ∀ ε ϖ : ℝ, 0 < ε → ε ≤ 1 → 1 < ϖ → ϖ ≤ Real.sqrt 2 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        [Measure.IsComplete P] (W : ℝ≥0 → Ω → Fin d → ℝ) (hW : Peng1990.SMP.IsStdBrownian P W)
        (η : ℝ → Matrix (Fin d) (Fin d) ℝ), IsRiccatiSol Q R T η →
      ∀ (m₀ : Fin d → ℝ) (m : ℝ≥0 → Ω → Fin d → ℝ), IsForwardLimit hW T η ε m₀ m →
      ∀ (mbar h : ℕ → ℝ≥0 → Ω → Fin d → ℝ) (k : ℕ → ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ),
        IsScheme hW T η (tmul Q f) (tmul R g) ε ϖ m₀ mbar h k →
      ∀ (hϖ : ℝ≥0 → Ω → Fin d → ℝ) (kϖ : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ),
        IsLimitBdd hW T η (tmul Q f) (tmul R g) ε ϖ m hϖ kϖ →
        ∀ᵐ ω ∂P, ∀ t ≤ T,
          eNorm (ϖ • hϖ t ω) ≤ C₂ ∧ ∀ n : ℕ, 1 ≤ n → eNorm (h n t ω) ≤ C₂ := by sorry

end ExploreLQMFG
