-- Prove2me | Theorems.Thm_ExploreLQMFG_theorem_2_4
-- name    : ExploreLQMFG.theorem_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:13:43.38738+00:00
-- url     : https://prove2.me/theorems/eeb6f8f9-2927-4cc4-b7ab-2552f770f6d1
-- title:
--   Theorem 2.4 — the tilted geometric fictitious play converges to (2.11) at rate $\varpi^{-n}e^{C/\varepsilon^2}$ (corrected: $F(m,h^\varpi)$ in (2.13))
-- statement:
--   Fix $d\ge1$, $T>0$ and bounds $L_f,L_g$. There is a constant $C$ such that the following holds for all $d\times d$ matrices $Q,R$, all bounded Lipschitz $f,g:\mathbb R^d\to\mathbb R^d$ with $\|Q^\dagger f\|_{1,\infty}\le L_f$ and $\|R^\dagger g\|_{1,\infty}\le L_g$, every common-noise intensity $\varepsilon\in(0,1]$, every learning rate $\varpi\in(1,\sqrt2]$, every complete probability space carrying a $d$-dimensional Brownian motion $W$, the solution $\eta$ of the Riccati equation (2.3), every $m_0=\mathbb E(X_0)\in\mathbb R^d$, the solution $m$ of
--   $$dm_t=-\eta_tm_t\,dt+\varepsilon\,dW_t,\qquad m_0\text{ given},$$
--   and every solution $(\bar m^n,h^n,k^n)_n$ of the tilted geometric fictitious play (2.10), started from any adapted continuous $\bar m^0$ and any adapted continuous bounded $h^0$:
--
--   1. the backward equation of (2.11),
--   $$dh^\varpi_t=\Big(-\frac1\varpi Q^\dagger f(m_t)+\eta_th^\varpi_t+\varpi k^\varpi_th^\varpi_t\Big)dt+\varepsilon k^\varpi_t\,dW_t,\qquad h^\varpi_T=\frac1\varpi R^\dagger g(m_T),$$
--   has a solution $(h^\varpi,k^\varpi)$ in the class of bounded processes;
--   2. for every such solution and every $n\ge1$,
--   $$\operatorname*{ess\,sup}_{\omega\in\Omega}\Big[\sup_{0\le t\le T}\big(|m_t-\bar m^n_t|^2+|h^\varpi_t-h^n_t|^2\big)\Big]\le\varpi^{-2n}\exp\Big(\frac C{\varepsilon^2}\Big);$$
--   3. for every such solution, every $n\ge0$ and every $F$ on $\mathcal C([0,T];\mathbb R^d\times\mathbb R^d)$ bounded by $1$ and $1$-Lipschitz,
--   $$\Big|\mathbb E^{\varpi h^n/\varepsilon}\big[F(\bar m^n,h^n)\big]-\mathbb E^{\varpi h^\varpi/\varepsilon}\big[F(m,h^\varpi)\big]\Big|\le\varpi^{-n}\exp\Big(\frac C{\varepsilon^2}\Big),$$
--   where $\mathbb E^{H/\varepsilon}$ is the expectation under the tilted measure (1.15).
--
--   The pair $(m,\varpi h^\varpi)$ is the equilibrium of the linear-quadratic mean field game with common noise of intensity $\varepsilon$, so the theorem says that the fictitious play, with the common noise used as exploration noise, learns the equilibrium at a geometric rate, with no potential or monotone structure on $f,g$.
--
--   Differences from the source:
--   - correction: (2.13) compares with E^{ϖh^ϖ/ε}[F(m, h)], bold h = ϖh^ϖ (defined right after the theorem) → E^{ϖh^ϖ/ε}[F(m, h^ϖ)]; reason: with h = ϖh^ϖ inside F the bound is false: d = 1, T = 1, Q = 0, R = 1, f ≡ 0, g ≡ 1/2, η_t = 1/(2 − t) give the bounded limit h^ϖ_t = 1/(2ϖ(2 − t)), k^ϖ = 0, and (hⁿ, kⁿ) = (h^ϖ, 0) for n ≥ 1 solves (2.10); for F(x, y) = max(−1, min(1, y(0))) the left side is (ϖ − 1)/(4ϖ) > 0 for every n while the right side tends to 0; the proof's last step (p.26) uses (2.12), which controls hⁿ − h^ϖ
--   - reading: n unquantified in (2.12) and (2.13) → (2.12) for every n ≥ 1, (2.13) for every n ≥ 0; reason: at n = 0 (2.12) fails for the typical m̄⁰ ≡ 𝔼(X₀) (m_t is Gaussian with positive variance); Lemma 2.10, (2.27) and Theorem 2.27 use n ≥ 1; (2.13) at n = 0 holds once exp(C/ε²) ≥ 2
--   - generalization: 'the scheme (2.10) converges to the decoupled version of the FBSDE system (2.11)' → an added clause 0: the backward equation of (2.11) has a solution in the bounded class; reason: existence is implicit in 'converges to' and asserted on p.22; dropping the clause gives the source's two bounds
--   - encoding: the Fortet–Mourier class on C([0, T]; ℝᵈ × ℝᵈ), norm on ℝᵈ × ℝᵈ unnamed → 1-Lipschitz for sup_t of the Euclidean norm of ℝ^{2d}; reason: any other product norm changes the class by a factor at most √2, absorbed in C
--   - encoding: ℙ^{H/ε} = ℰ((1/ε)H)·ℙ with ℰ((1/ε)H) = exp(−(1/ε)∫₀ᵀ H·dW − (1/(2ε²))∫₀ᵀ|H|²dt) (1.15) → tilt: Measure.withDensity of that exponential, with ∫₀ᵀ H·dW = Σⱼ (value at T of a chosen Peng1990.SMP Itô integral process of Hʲ against Wʲ); reason: the Itô integral is unique a.s., so every choice gives the same measure
--   - reading: the solution classes are left implicit: hⁿ⁺¹ ∈ S^d(𝔽^W) (Lemma 2.1(ii)), kⁿ⁺¹ progressive; (2.11) solved 'in the class of bounded processes' (p.22) → scheme: m̄ⁿ, hⁿ adapted with continuous paths, (hⁿ⁺¹, kⁿ⁺¹) in L²_𝔽 (Peng1990.SMP.SolvesBSDE); limit: h^ϖ continuous with a deterministic a.s. bound, k^ϖ bounded dt⊗dℙ-a.e.; reason: the standard BSDE class for the scheme and the class in which p.22 asserts uniqueness for the limit
--   - reading: 'The two initial processes m⁰ and h⁰ are two 𝔽^W-adapted continuous processes' (p.19), with the tilted measure ℙ^{ϖh⁰/ε} used as a probability measure → m̄⁰ any adapted process with continuous paths; h⁰ any adapted process with continuous paths and a deterministic almost-sure bound on [0, T]; reason: boundedness is what makes ℙ^{ϖh⁰/ε} a probability measure (Novikov); it contains the paper's choice h⁰ = 0, and the constants do not depend on the bound
--   - encoding: time t ∈ [0, T], processes indexed by [0, T] → processes indexed by ℝ≥0, [0, T] cut out by t ≤ T; time integrals over [0, t] ⊂ ℝ; reason: Lean convention of the published Peng1990.SMP stochastic-calculus definitions; values after T never enter
--   - encoding: ℝᵈ with the Euclidean norm |·|; |·| on d × d matrices unnamed → Fin d → ℝ with |x|² = Σᵢ xᵢ² written explicitly; matrices carry the Frobenius norm; reason: Mathlib's default norm on Fin d → ℝ is the sup norm; all matrix norms are equivalent up to a factor depending only on d, which the constants absorb
--   - encoding: a constant depending only on d, T, ‖Q†f‖_{1,∞} and ‖R†g‖_{1,∞} → for every d ≥ 1, T > 0 and bounds L_f, L_g there is a constant valid for all Q, R, f, g with ‖Q†f‖_{1,∞} ≤ L_f and ‖R†g‖_{1,∞} ≤ L_g, all ε, ϖ and all data; reason: the uniform form of 'depends only on'; it is at least as strong as a function of the exact norms
--   - encoding: m₀ = 𝔼(X₀), with X₀, the idiosyncratic noise B and its intensity σ in the model → an arbitrary vector m₀ ∈ ℝᵈ; X₀, B and σ are not part of the data; reason: only 𝔼(X₀) enters (2.9)–(2.13); every m₀ ∈ ℝᵈ is 𝔼(X₀) for X₀ ≡ m₀
--   - encoding: the augmented filtration 𝔽^W of W on a complete probability space → augFiltration: the natural filtration of W (published Peng1990.SMP.brownianFiltration) joined with the σ-algebra of P-null sets, with P.IsComplete assumed; reason: on a complete space this is the usual augmentation
-- source:
--   Delarue & Vasileiadis, Exploration Noise for Learning Linear-Quadratic Mean Field Games, arXiv:2107.00839v2 (https://arxiv.org/abs/2107.00839v2), Theorem 2.4, (2.10)–(2.13), p.21

import Mathlib
import Definitions.Def_ExploreLQMFG_Scheme
import Definitions.Def_ExploreLQMFG_Tilt
import Definitions.Def_ExploreLQMFG_FortetMourier

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Matrix

universe u

namespace ExploreLQMFG

/-- **Theorem 2.4** (Delarue & Vasileiadis, arXiv:2107.00839v2, p.21): the tilted geometric
fictitious play (2.10) converges to the decoupled FBSDE system (2.11), with
`essup_ω sup_{0≤t≤T} (|m_t − m̄ⁿ_t|² + |h^ϖ_t − hⁿ_t|²) ≤ ϖ^{−2n} exp(C/ε²)` (2.12) and the
Fortet–Mourier weak error
`sup_F |𝔼^{ϖhⁿ/ε}[F(m̄ⁿ, hⁿ)] − 𝔼^{ϖh^ϖ/ε}[F(m, h^ϖ)]| ≤ ϖ^{−n} exp(C/ε²)` (2.13), for a constant
`C` that depends on `d`, `T`, `‖Q†f‖_{1,∞}` and `‖R†g‖_{1,∞}`.

For every `d ≥ 1`, `T > 0` and bounds `L_f, L_g` there is `C` such that, for all `Q, R`, all
bounded Lipschitz `f, g` with `‖Q†f‖_{1,∞} ≤ L_f`, `‖R†g‖_{1,∞} ≤ L_g`, all `ε ∈ (0, 1]`,
`ϖ ∈ (1, √2]`, every complete probability space with a `d`-dimensional Brownian motion `W`,
the Riccati solution `η` (2.3), every `m₀ = 𝔼(X₀) ∈ ℝᵈ`, the solution `m` of
`dm_t = −η_t m_t dt + ε dW_t`, `m_0 = m₀`, and every solution `(m̄ⁿ, hⁿ, kⁿ)` of the scheme
(2.10) (any adapted continuous `m̄⁰`, any adapted continuous bounded `h⁰`):

0. the backward equation of (2.11) has a solution `(h^ϖ, k^ϖ)` in the class of bounded
   processes;
1. for every such solution and every `n ≥ 1`, almost surely, for all `t ∈ [0, T]`,
   `|m_t − m̄ⁿ_t|² + |h^ϖ_t − hⁿ_t|² ≤ ϖ^{−2n} exp(C/ε²)`;
2. for every such solution, every `n ≥ 0` and every `F` on `𝒞([0, T]; ℝᵈ × ℝᵈ)` bounded by 1
   and 1-Lipschitz, `|𝔼^{ϖhⁿ/ε}[F(m̄ⁿ, hⁿ)] − 𝔼^{ϖh^ϖ/ε}[F(m, h^ϖ)]| ≤ ϖ^{−n} exp(C/ε²)`.

One `C` serves (2.12) and (2.13).

**Formalization Note.**
1. (2.13) is printed with `F(m, h)`, bold `h = ϖh^ϖ` (defined after the theorem, p.21). With
   that reading the bound is false (d = 1, T = 1, Q = 0, R = 1, f ≡ 0, g ≡ 1/2: `hⁿ = h^ϖ` for
   all `n ≥ 1` and the gap is `(ϖ − 1)/(4ϖ)` for every `n`); the statement compares with
   `F(m, h^ϖ)`, which is what the proof's appeal to (2.12) on p.26 gives.
2. `n` is unquantified on the page: (2.12) is stated for `n ≥ 1` (at `n = 0` the initial proxy
   is arbitrary) and (2.13) for every `n ≥ 0`.
3. `𝔼^{ϖH/ε}` integrates against `tilt … ε (ϖ • H)` (1.15); the filtration is the augmented
   Brownian filtration; time is `ℝ≥0` with `[0, T]` cut out by `t ≤ T`; `|·|` is Euclidean. -/
theorem theorem_2_4 {d : ℕ} (hd : 0 < d) (T : ℝ≥0) (hT : 0 < T) (Lf Lg : ℝ) :
    ∃ C : ℝ, ∀ (Q R : Matrix (Fin d) (Fin d) ℝ) (f g : (Fin d → ℝ) → (Fin d → ℝ)),
      IsBddLip f → IsBddLip g → oneInfNorm (tmul Q f) ≤ Lf → oneInfNorm (tmul R g) ≤ Lg →
      ∀ ε ϖ : ℝ, 0 < ε → ε ≤ 1 → 1 < ϖ → ϖ ≤ Real.sqrt 2 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        [Measure.IsComplete P] (W : ℝ≥0 → Ω → Fin d → ℝ) (hW : Peng1990.SMP.IsStdBrownian P W)
        (η : ℝ → Matrix (Fin d) (Fin d) ℝ), IsRiccatiSol Q R T η →
      ∀ (m₀ : Fin d → ℝ) (m : ℝ≥0 → Ω → Fin d → ℝ), IsForwardLimit hW T η ε m₀ m →
      ∀ (mbar h : ℕ → ℝ≥0 → Ω → Fin d → ℝ) (k : ℕ → ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ),
        IsScheme hW T η (tmul Q f) (tmul R g) ε ϖ m₀ mbar h k →
        (∃ (hϖ : ℝ≥0 → Ω → Fin d → ℝ) (kϖ : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ),
          IsLimitBdd hW T η (tmul Q f) (tmul R g) ε ϖ m hϖ kϖ) ∧
        ∀ (hϖ : ℝ≥0 → Ω → Fin d → ℝ) (kϖ : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ),
          IsLimitBdd hW T η (tmul Q f) (tmul R g) ε ϖ m hϖ kϖ →
          (∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P, ∀ t ≤ T,
            eSq (m t ω - mbar n t ω) + eSq (hϖ t ω - h n t ω)
              ≤ ϖ ^ (-(2 * (n : ℤ))) * Real.exp (C / ε ^ 2)) ∧
          (∀ n : ℕ, ∀ F : PathSpace d T → ℝ, IsFortetMourier F →
            |(∫ ω, F (pathOf T (mbar n) (h n) ω)
                  ∂(tilt (augFiltration hW) P T W ε (fun s ω => ϖ • h n s ω)))
              - ∫ ω, F (pathOf T m hϖ ω)
                  ∂(tilt (augFiltration hW) P T W ε (fun s ω => ϖ • hϖ s ω))|
              ≤ ϖ ^ (-(n : ℤ)) * Real.exp (C / ε ^ 2)) := by sorry

end ExploreLQMFG
