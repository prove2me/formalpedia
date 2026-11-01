-- Prove2me | Theorems.Thm_ExploreLQMFG_eq_2_20
-- name    : ExploreLQMFG.eq_2_20
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:13:46.159984+00:00
-- url     : https://prove2.me/theorems/083f4a63-3597-4da4-a93a-81e2a99cb65c
-- title:
--   (2.20), p.24 — $\sup_{0\le t\le T}|\bar m^n_t-m_t|\le C\varpi^{-n}$
-- statement:
--   Fix $d\ge1$, $T>0$ and bounds $L_f,L_g$. There is a constant $C$ such that for all $Q,R$, all bounded Lipschitz $f,g$ with $\|Q^\dagger f\|_{1,\infty}\le L_f$, $\|R^\dagger g\|_{1,\infty}\le L_g$, all $\varepsilon\in(0,1]$, $\varpi\in(1,\sqrt2]$, every complete probability space with a $d$-dimensional Brownian motion, the Riccati solution $\eta$, every $m_0\in\mathbb R^d$, the forward solution $m$ of (2.11) and every solution $(\bar m^n,h^n,k^n)$ of the scheme (2.10), for every $n\ge1$, almost surely,
--   $$\sup_{0\le t\le T}|\bar m^n_t-m_t|\le C\varpi^{-n}.$$
--
--   This is the forward half of the convergence: the averaged proxy approaches the equilibrium mean at the geometric rate, because the weight of $h^{n}$ in the forward equation decays like $\varpi^{-n}$ while $h^n$ stays bounded (Lemma 2.10).
--
--   Differences from the source:
--   - reading: n unquantified in (2.20) → every n ≥ 1; reason: the step uses (2.19) at n − 1 and Lemma 2.10 (n ≥ 1); at n = 0 the initial proxy m̄⁰ is arbitrary (typically the constant 𝔼(X₀)) and the bound fails
--   - reading: the solution classes are left implicit: hⁿ⁺¹ ∈ S^d(𝔽^W) (Lemma 2.1(ii)), kⁿ⁺¹ progressive; (2.11) solved 'in the class of bounded processes' (p.22) → scheme: m̄ⁿ, hⁿ adapted with continuous paths, (hⁿ⁺¹, kⁿ⁺¹) in L²_𝔽 (Peng1990.SMP.SolvesBSDE); limit: h^ϖ continuous with a deterministic a.s. bound, k^ϖ bounded dt⊗dℙ-a.e.; reason: the standard BSDE class for the scheme and the class in which p.22 asserts uniqueness for the limit
--   - reading: 'The two initial processes m⁰ and h⁰ are two 𝔽^W-adapted continuous processes' (p.19), with the tilted measure ℙ^{ϖh⁰/ε} used as a probability measure → m̄⁰ any adapted process with continuous paths; h⁰ any adapted process with continuous paths and a deterministic almost-sure bound on [0, T]; reason: boundedness is what makes ℙ^{ϖh⁰/ε} a probability measure (Novikov); it contains the paper's choice h⁰ = 0, and the constants do not depend on the bound
--   - encoding: time t ∈ [0, T], processes indexed by [0, T] → processes indexed by ℝ≥0, [0, T] cut out by t ≤ T; time integrals over [0, t] ⊂ ℝ; reason: Lean convention of the published Peng1990.SMP stochastic-calculus definitions; values after T never enter
--   - encoding: ℝᵈ with the Euclidean norm |·|; |·| on d × d matrices unnamed → Fin d → ℝ with |x|² = Σᵢ xᵢ² written explicitly; matrices carry the Frobenius norm; reason: Mathlib's default norm on Fin d → ℝ is the sup norm; all matrix norms are equivalent up to a factor depending only on d, which the constants absorb
--   - encoding: a constant depending only on d, T, ‖Q†f‖_{1,∞} and ‖R†g‖_{1,∞} → for every d ≥ 1, T > 0 and bounds L_f, L_g there is a constant valid for all Q, R, f, g with ‖Q†f‖_{1,∞} ≤ L_f and ‖R†g‖_{1,∞} ≤ L_g, all ε, ϖ and all data; reason: the uniform form of 'depends only on'; it is at least as strong as a function of the exact norms
--   - encoding: m₀ = 𝔼(X₀), with X₀, the idiosyncratic noise B and its intensity σ in the model → an arbitrary vector m₀ ∈ ℝᵈ; X₀, B and σ are not part of the data; reason: only 𝔼(X₀) enters (2.9)–(2.13); every m₀ ∈ ℝᵈ is 𝔼(X₀) for X₀ ≡ m₀
--   - encoding: the augmented filtration 𝔽^W of W on a complete probability space → augFiltration: the natural filtration of W (published Peng1990.SMP.brownianFiltration) joined with the σ-algebra of P-null sets, with P.IsComplete assumed; reason: on a complete space this is the usual augmentation
-- source:
--   Delarue & Vasileiadis, Exploration Noise for Learning Linear-Quadratic Mean Field Games, arXiv:2107.00839v2 (https://arxiv.org/abs/2107.00839v2), Proof of Theorem 2.4, First Step, (2.19)–(2.20), p.24

import Mathlib
import Definitions.Def_ExploreLQMFG_Scheme

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Matrix

universe u

namespace ExploreLQMFG

/-- **The forward error (2.20)** (Delarue & Vasileiadis, arXiv:2107.00839v2, proof of
Theorem 2.4, First Step, p.24): "Invoking Lemma 2.10 and recalling that ϖ ∈ (1, √2], we then
have |((1−ϖ⁻¹)ϖ⁻ⁿ/(1−ϖ^{−(n+1)})) hⁿ⁺¹_t| ≤ Cϖ⁻ⁿ (2.19), from which we deduce (consider the
difference between (2.9) and the forward equation in (2.11)) that
sup_{0≤t≤T} |m̄ⁿ_t − m_t| ≤ Cϖ⁻ⁿ (2.20)", where "C is a generic constant … [that] only depends
on d, T, ‖Q†f‖_{1,∞} and ‖R†g‖_{1,∞}".

For every scheme solution (2.10) and the solution `m` of the forward equation of (2.11), almost
surely, `|m̄ⁿ_t − m_t| ≤ Cϖ⁻ⁿ` for all `t ∈ [0, T]`, for every `n ≥ 1`.

**Formalization Note.** `n ≥ 1`: at `n = 0`, `m̄⁰` is the arbitrary initial proxy (typically
the constant `𝔼(X₀)`), and the bound fails. `C` is quantified before everything except
`d, T` and bounds `L_f, L_g` on the norms. -/
theorem eq_2_20 {d : ℕ} (hd : 0 < d) (T : ℝ≥0) (hT : 0 < T) (Lf Lg : ℝ) :
    ∃ C : ℝ, ∀ (Q R : Matrix (Fin d) (Fin d) ℝ) (f g : (Fin d → ℝ) → (Fin d → ℝ)),
      IsBddLip f → IsBddLip g → oneInfNorm (tmul Q f) ≤ Lf → oneInfNorm (tmul R g) ≤ Lg →
      ∀ ε ϖ : ℝ, 0 < ε → ε ≤ 1 → 1 < ϖ → ϖ ≤ Real.sqrt 2 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        [Measure.IsComplete P] (W : ℝ≥0 → Ω → Fin d → ℝ) (hW : Peng1990.SMP.IsStdBrownian P W)
        (η : ℝ → Matrix (Fin d) (Fin d) ℝ), IsRiccatiSol Q R T η →
      ∀ (m₀ : Fin d → ℝ) (m : ℝ≥0 → Ω → Fin d → ℝ), IsForwardLimit hW T η ε m₀ m →
      ∀ (mbar h : ℕ → ℝ≥0 → Ω → Fin d → ℝ) (k : ℕ → ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ),
        IsScheme hW T η (tmul Q f) (tmul R g) ε ϖ m₀ mbar h k →
      ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P, ∀ t ≤ T,
        eNorm (mbar n t ω - m t ω) ≤ C * ϖ ^ (-(n : ℤ)) := by sorry

end ExploreLQMFG
