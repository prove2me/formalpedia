-- Prove2me | Theorems.Thm_ExploreLQMFG_eq_2_28
-- name    : ExploreLQMFG.eq_2_28
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:13:40.324807+00:00
-- url     : https://prove2.me/theorems/04267970-60cd-407e-973a-1d8d864d55af
-- title:
--   (2.28), p.26 — $d_{TV}(\mathbb P^{h/\varepsilon},\mathbb P^{\varpi h^n/\varepsilon})\le\frac C\varepsilon\varpi^{-n}\exp(\frac C{2\varepsilon^2})$
-- statement:
--   Fix $d\ge1$, $T>0$ and bounds $L_f,L_g$. There is a constant $C$ such that for all $Q,R$, all bounded Lipschitz $f,g$ with $\|Q^\dagger f\|_{1,\infty}\le L_f$, $\|R^\dagger g\|_{1,\infty}\le L_g$, all $\varepsilon\in(0,1]$, $\varpi\in(1,\sqrt2]$, every complete probability space with a $d$-dimensional Brownian motion, the Riccati solution $\eta$, every $m_0$, the forward solution $m$, every solution $(\bar m^n,h^n,k^n)$ of (2.10) and every bounded solution $(h^\varpi,k^\varpi)$ of (2.11), with $h=\varpi h^\varpi$, and every $n\ge0$,
--   $$d_{TV}\big(\mathbb P^{h/\varepsilon},\mathbb P^{\varpi h^n/\varepsilon}\big)\le\frac C\varepsilon\,\varpi^{-n}\exp\Big(\frac C{2\varepsilon^2}\Big),$$
--   where $d_{TV}(\mu,\nu)=\sup_A|\mu(A)-\nu(A)|$ is the total variation distance and $\mathbb P^{H/\varepsilon}$ the tilted measure (1.15).
--
--   This is the passage from the strong error (2.12) to the weak error (2.13): the two tilted measures, under which the scheme and the equilibrium are compared, are close in total variation.
--
--   Differences from the source:
--   - reading: n unquantified in (2.28) → every n ≥ 0; reason: at n = 0 the bound holds once C ≥ 1, since d_TV ≤ 1 ≤ (C/ε)exp(C/(2ε²)) for ε ≤ 1; it matches (2.13), stated for n ≥ 0
--   - encoding: d_TV, 'the total variation distance' → the published FoundationsRL.DECLower.tvDist, sup over measurable A of |μ(A) − ν(A)|; reason: the same definition
--   - encoding: h = ϖh^ϖ, the intercept of (2.15)–(2.16), defined through the bounded solution of (2.11) → h := ϖ • h^ϖ for an arbitrary solution (h^ϖ, k^ϖ) of the backward equation of (2.11) in the bounded class; reason: the change of variable (2.17); the bounded solution is unique (p.22)
--   - encoding: ℙ^{H/ε} = ℰ((1/ε)H)·ℙ with ℰ((1/ε)H) = exp(−(1/ε)∫₀ᵀ H·dW − (1/(2ε²))∫₀ᵀ|H|²dt) (1.15) → tilt: Measure.withDensity of that exponential, with ∫₀ᵀ H·dW = Σⱼ (value at T of a chosen Peng1990.SMP Itô integral process of Hʲ against Wʲ); reason: the Itô integral is unique a.s., so every choice gives the same measure
--   - reading: the solution classes are left implicit: hⁿ⁺¹ ∈ S^d(𝔽^W) (Lemma 2.1(ii)), kⁿ⁺¹ progressive; (2.11) solved 'in the class of bounded processes' (p.22) → scheme: m̄ⁿ, hⁿ adapted with continuous paths, (hⁿ⁺¹, kⁿ⁺¹) in L²_𝔽 (Peng1990.SMP.SolvesBSDE); limit: h^ϖ continuous with a deterministic a.s. bound, k^ϖ bounded dt⊗dℙ-a.e.; reason: the standard BSDE class for the scheme and the class in which p.22 asserts uniqueness for the limit
--   - reading: 'The two initial processes m⁰ and h⁰ are two 𝔽^W-adapted continuous processes' (p.19), with the tilted measure ℙ^{ϖh⁰/ε} used as a probability measure → m̄⁰ any adapted process with continuous paths; h⁰ any adapted process with continuous paths and a deterministic almost-sure bound on [0, T]; reason: boundedness is what makes ℙ^{ϖh⁰/ε} a probability measure (Novikov); it contains the paper's choice h⁰ = 0, and the constants do not depend on the bound
--   - encoding: time t ∈ [0, T], processes indexed by [0, T] → processes indexed by ℝ≥0, [0, T] cut out by t ≤ T; time integrals over [0, t] ⊂ ℝ; reason: Lean convention of the published Peng1990.SMP stochastic-calculus definitions; values after T never enter
--   - encoding: ℝᵈ with the Euclidean norm |·|; |·| on d × d matrices unnamed → Fin d → ℝ with |x|² = Σᵢ xᵢ² written explicitly; matrices carry the Frobenius norm; reason: Mathlib's default norm on Fin d → ℝ is the sup norm; all matrix norms are equivalent up to a factor depending only on d, which the constants absorb
--   - encoding: a constant depending only on d, T, ‖Q†f‖_{1,∞} and ‖R†g‖_{1,∞} → for every d ≥ 1, T > 0 and bounds L_f, L_g there is a constant valid for all Q, R, f, g with ‖Q†f‖_{1,∞} ≤ L_f and ‖R†g‖_{1,∞} ≤ L_g, all ε, ϖ and all data; reason: the uniform form of 'depends only on'; it is at least as strong as a function of the exact norms
--   - encoding: m₀ = 𝔼(X₀), with X₀, the idiosyncratic noise B and its intensity σ in the model → an arbitrary vector m₀ ∈ ℝᵈ; X₀, B and σ are not part of the data; reason: only 𝔼(X₀) enters (2.9)–(2.13); every m₀ ∈ ℝᵈ is 𝔼(X₀) for X₀ ≡ m₀
--   - encoding: the augmented filtration 𝔽^W of W on a complete probability space → augFiltration: the natural filtration of W (published Peng1990.SMP.brownianFiltration) joined with the σ-algebra of P-null sets, with P.IsComplete assumed; reason: on a complete space this is the usual augmentation
-- source:
--   Delarue & Vasileiadis, Exploration Noise for Learning Linear-Quadratic Mean Field Games, arXiv:2107.00839v2 (https://arxiv.org/abs/2107.00839v2), Proof of Theorem 2.4, Second Step, (2.28), pp.25–26

import Mathlib
import Definitions.Def_ExploreLQMFG_Scheme
import Definitions.Def_ExploreLQMFG_Tilt
import Definitions.Def_FoundationsRL_DECLower_tvDist

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Matrix

universe u

namespace ExploreLQMFG

/-- **The total-variation bound (2.28)** (Delarue & Vasileiadis, arXiv:2107.00839v2, proof of
Theorem 2.4, Second Step, pp.25–26): `d_TV(ℙ^{h/ε}, ℙ^{ϖhⁿ/ε}) ≤ (C/ε) ϖ⁻ⁿ exp(C/(2ε²))`, where
`d_TV` is the total variation distance, `h = ϖh^ϖ` for a bounded solution `(h^ϖ, k^ϖ)` of (2.11),
`hⁿ` is the scheme (2.10), and `ℙ^{H/ε}` is the tilted measure (1.15).

**Formalization Note.**
1. `d_TV(μ, ν) = sup_A |μ(A) − ν(A)|` is the published `FoundationsRL.DECLower.tvDist`.
2. `C` only depends on `d, T` and the norms ("C is a generic constant … only depends on d, T,
   ‖Q†f‖_{1,∞} and ‖R†g‖_{1,∞}", p.24), encoded as `∃ C` after `d, T` and bounds `L_f, L_g`.
3. The page does not quantify `n`; the statement is for every `n ≥ 0`. -/
theorem eq_2_28 {d : ℕ} (hd : 0 < d) (T : ℝ≥0) (hT : 0 < T) (Lf Lg : ℝ) :
    ∃ C : ℝ, ∀ (Q R : Matrix (Fin d) (Fin d) ℝ) (f g : (Fin d → ℝ) → (Fin d → ℝ)),
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
      ∀ n : ℕ,
        FoundationsRL.DECLower.tvDist
            (tilt (augFiltration hW) P T W ε (fun s ω => ϖ • hϖ s ω))
            (tilt (augFiltration hW) P T W ε (fun s ω => ϖ • h n s ω))
          ≤ C / ε * ϖ ^ (-(n : ℤ)) * Real.exp (C / (2 * ε ^ 2)) := by sorry

end ExploreLQMFG
