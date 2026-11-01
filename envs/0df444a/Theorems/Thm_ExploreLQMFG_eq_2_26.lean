-- Prove2me | Theorems.Thm_ExploreLQMFG_eq_2_26
-- name    : ExploreLQMFG.eq_2_26
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:13:26.836448+00:00
-- url     : https://prove2.me/theorems/03fe0667-2ce1-463d-84c9-163cceb9d7a0
-- title:
--   (2.26), p.25 — one-step contraction of $h^{n+1}-h^\varpi$ under $\mathbb P^{h/\varepsilon}$ with factor $1/3$
-- statement:
--   Fix $d\ge1$, $T>0$ and bounds $L_f,L_g$. There is a constant $C>0$ (the constant of (2.23)) such that for all $Q,R$, all bounded Lipschitz $f,g$ with $\|Q^\dagger f\|_{1,\infty}\le L_f$, $\|R^\dagger g\|_{1,\infty}\le L_g$, all $\varepsilon\in(0,1]$, $\varpi\in(1,\sqrt2]$, every complete probability space with a $d$-dimensional Brownian motion and augmented filtration $(\mathcal F_t)$, the Riccati solution $\eta$, every $m_0$, the forward solution $m$, every solution $(\bar m^n,h^n,k^n)$ of (2.10) and every bounded solution $(h^\varpi,k^\varpi)$ of (2.11), with $h=\varpi h^\varpi$, for every $n\ge1$ and every $t\in[0,T]$, almost surely,
--   $$\frac{\varepsilon^2}{3C}e^{\frac{4C}{\varepsilon^2}t}|h^{n+1}_t-h^\varpi_t|^2+\mathbb E^{h/\varepsilon}\Big[\int_t^Te^{\frac{4C}{\varepsilon^2}s}|h^{n+1}_s-h^\varpi_s|^2ds\,\Big|\,\mathcal F_t\Big]
--   \le\frac{\varepsilon^2(1+T)}3\varpi^{-2n}e^{\frac{4C}{\varepsilon^2}T}+\frac13\mathbb E^{h/\varepsilon}\Big[\int_t^Te^{\frac{4C}{\varepsilon^2}s}|h^n_s-h^\varpi_s|^2ds\,\Big|\,\mathcal F_t\Big].$$
--   Here $\mathbb E^{h/\varepsilon}[\cdot\,|\,\mathcal F_t]$ is the conditional expectation under the tilted measure $\mathbb P^{h/\varepsilon}$ of (1.15).
--
--   Iterating this contraction (the factor $1/3<\varpi^{-2}$ because $\varpi\le\sqrt2$) gives (2.27) and then the strong bound (2.12).
--
--   Differences from the source:
--   - encoding: 'holds true for almost every ω ∈ Ω (under ℙ and ℙ^{h/ε}) and for every t ∈ [0, T]' → for every t ∈ [0, T], ℙ-almost surely; reason: a conditional expectation is defined up to a null set for each fixed t; ℙ-a.s. implies ℙ^{h/ε}-a.s.
--   - encoding: 'a constant C as in the statement' of (2.23), depending only on d, T and the norms → ∃ C > 0 quantified before every quantity except d, T and the bounds L_f, L_g; reason: the constant of (2.23) is not given explicitly; the milestone asserts the inequality for some such constant
--   - reading: n unquantified in (2.26) → every n ≥ 1; reason: the derivation uses (2.20) at n, which needs n ≥ 1
--   - encoding: h = ϖh^ϖ, the intercept of (2.15)–(2.16), defined through the bounded solution of (2.11) → h := ϖ • h^ϖ for an arbitrary solution (h^ϖ, k^ϖ) of the backward equation of (2.11) in the bounded class; reason: the change of variable (2.17); the bounded solution is unique (p.22)
--   - encoding: ℙ^{H/ε} = ℰ((1/ε)H)·ℙ with ℰ((1/ε)H) = exp(−(1/ε)∫₀ᵀ H·dW − (1/(2ε²))∫₀ᵀ|H|²dt) (1.15) → tilt: Measure.withDensity of that exponential, with ∫₀ᵀ H·dW = Σⱼ (value at T of a chosen Peng1990.SMP Itô integral process of Hʲ against Wʲ); reason: the Itô integral is unique a.s., so every choice gives the same measure
--   - reading: the solution classes are left implicit: hⁿ⁺¹ ∈ S^d(𝔽^W) (Lemma 2.1(ii)), kⁿ⁺¹ progressive; (2.11) solved 'in the class of bounded processes' (p.22) → scheme: m̄ⁿ, hⁿ adapted with continuous paths, (hⁿ⁺¹, kⁿ⁺¹) in L²_𝔽 (Peng1990.SMP.SolvesBSDE); limit: h^ϖ continuous with a deterministic a.s. bound, k^ϖ bounded dt⊗dℙ-a.e.; reason: the standard BSDE class for the scheme and the class in which p.22 asserts uniqueness for the limit
--   - reading: 'The two initial processes m⁰ and h⁰ are two 𝔽^W-adapted continuous processes' (p.19), with the tilted measure ℙ^{ϖh⁰/ε} used as a probability measure → m̄⁰ any adapted process with continuous paths; h⁰ any adapted process with continuous paths and a deterministic almost-sure bound on [0, T]; reason: boundedness is what makes ℙ^{ϖh⁰/ε} a probability measure (Novikov); it contains the paper's choice h⁰ = 0, and the constants do not depend on the bound
--   - encoding: time t ∈ [0, T], processes indexed by [0, T] → processes indexed by ℝ≥0, [0, T] cut out by t ≤ T; time integrals over [0, t] ⊂ ℝ; reason: Lean convention of the published Peng1990.SMP stochastic-calculus definitions; values after T never enter
--   - encoding: ℝᵈ with the Euclidean norm |·|; |·| on d × d matrices unnamed → Fin d → ℝ with |x|² = Σᵢ xᵢ² written explicitly; matrices carry the Frobenius norm; reason: Mathlib's default norm on Fin d → ℝ is the sup norm; all matrix norms are equivalent up to a factor depending only on d, which the constants absorb
--   - encoding: m₀ = 𝔼(X₀), with X₀, the idiosyncratic noise B and its intensity σ in the model → an arbitrary vector m₀ ∈ ℝᵈ; X₀, B and σ are not part of the data; reason: only 𝔼(X₀) enters (2.9)–(2.13); every m₀ ∈ ℝᵈ is 𝔼(X₀) for X₀ ≡ m₀
--   - encoding: the augmented filtration 𝔽^W of W on a complete probability space → augFiltration: the natural filtration of W (published Peng1990.SMP.brownianFiltration) joined with the σ-algebra of P-null sets, with P.IsComplete assumed; reason: on a complete space this is the usual augmentation
-- source:
--   Delarue & Vasileiadis, Exploration Noise for Learning Linear-Quadratic Mean Field Games, arXiv:2107.00839v2 (https://arxiv.org/abs/2107.00839v2), Proof of Theorem 2.4, First Step, (2.23)–(2.26), p.25

import Mathlib
import Definitions.Def_ExploreLQMFG_Scheme
import Definitions.Def_ExploreLQMFG_Tilt

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Matrix

universe u

namespace ExploreLQMFG

/-- **The one-step contraction (2.26)** (Delarue & Vasileiadis, arXiv:2107.00839v2, proof of
Theorem 2.4, First Step, p.25), with `λ = 4` in (2.25) and `C` "a constant as in the statement"
of (2.23), which only depends on `d`, `T`, `‖Q†f‖_{1,∞}` and `‖R†g‖_{1,∞}`:

`(ε²/(3C)) exp((4C/ε²)t) |hⁿ⁺¹_t − h^ϖ_t|²
   + 𝔼^{h/ε}[∫ₜᵀ exp((4C/ε²)s) |hⁿ⁺¹_s − h^ϖ_s|² ds | 𝓕_t]
 ≤ (ε²(1+T)/3) ϖ^{−2n} exp((4C/ε²)T)
   + (1/3) 𝔼^{h/ε}[∫ₜᵀ exp((4C/ε²)s) |hⁿ_s − h^ϖ_s|² ds | 𝓕_t]`.

Here `hⁿ` is the scheme (2.10), `(h^ϖ, k^ϖ)` a bounded solution of (2.11), `h = ϖh^ϖ`,
`𝔼^{h/ε}[· | 𝓕_t]` the conditional expectation under the tilted measure `ℙ^{h/ε}` of (1.15)
given `𝓕_t` (the augmented Brownian filtration), and `n ≥ 1`.

**Formalization Note.**
1. The page says (2.26) "holds true for almost every ω ∈ Ω (under ℙ and ℙ^{h/ε}) and for every
   t ∈ [0, T]". A conditional expectation is defined up to a null set for each fixed `t`, so the
   statement is: for every `t ∈ [0, T]`, `ℙ`-almost surely (hence `ℙ^{h/ε}`-almost surely,
   since `ℙ^{h/ε} ≪ ℙ`).
2. `C > 0` is existential, before every quantity except `d, T` and bounds `L_f, L_g` on the
   norms.
3. `n ≥ 1`: the derivation uses (2.20) at `n`, which needs `n ≥ 1`. -/
theorem eq_2_26 {d : ℕ} (hd : 0 < d) (T : ℝ≥0) (hT : 0 < T) (Lf Lg : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q R : Matrix (Fin d) (Fin d) ℝ) (f g : (Fin d → ℝ) → (Fin d → ℝ)),
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
      ∀ n : ℕ, 1 ≤ n → ∀ t ≤ T, ∀ᵐ ω ∂P,
        ε ^ 2 / (3 * C) * Real.exp (4 * C / ε ^ 2 * t) * eSq (h (n + 1) t ω - hϖ t ω)
          + (tilt (augFiltration hW) P T W ε (fun s ω => ϖ • hϖ s ω))[
              fun ω => ∫ s in Set.Icc (t : ℝ) T,
                Real.exp (4 * C / ε ^ 2 * s) * eSq (h (n + 1) s.toNNReal ω - hϖ s.toNNReal ω)
              | augFiltration hW t] ω
        ≤ ε ^ 2 * (1 + T) / 3 * ϖ ^ (-(2 * (n : ℤ))) * Real.exp (4 * C / ε ^ 2 * T)
          + 1 / 3 * (tilt (augFiltration hW) P T W ε (fun s ω => ϖ • hϖ s ω))[
              fun ω => ∫ s in Set.Icc (t : ℝ) T,
                Real.exp (4 * C / ε ^ 2 * s) * eSq (h n s.toNNReal ω - hϖ s.toNNReal ω)
              | augFiltration hW t] ω := by sorry

end ExploreLQMFG
