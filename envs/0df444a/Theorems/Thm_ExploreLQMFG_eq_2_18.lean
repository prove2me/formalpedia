-- Prove2me | Theorems.Thm_ExploreLQMFG_eq_2_18
-- name    : ExploreLQMFG.eq_2_18
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:14:06.89357+00:00
-- url     : https://prove2.me/theorems/12408929-0810-4a77-8d44-70318f90acd6
-- title:
--   (2.18), p.22 — the bounded solution of (2.11) is $h^\varpi_t=\theta_\varepsilon(t,m_t)/\varpi$, $k^\varpi_t=\nabla_x\theta_\varepsilon(t,m_t)/\varpi$, and it is unique
-- statement:
--   Fix $d\ge1$, $T>0$ and bounds $L_f,L_g$. There is a constant $C_0$ such that the following holds for all $d\times d$ matrices $Q,R$, all bounded Lipschitz $f,g$ with $\|Q^\dagger f\|_{1,\infty}\le L_f$, $\|R^\dagger g\|_{1,\infty}\le L_g$, all $\varepsilon\in(0,1]$, $\varpi\in(1,\sqrt2]$, every complete probability space carrying a $d$-dimensional Brownian motion $W$, the Riccati solution $\eta$, every $m_0\in\mathbb R^d$, the solution $m$ of $dm_t=-\eta_tm_t\,dt+\varepsilon\,dW_t$, $m_0$ given, and every classical solution $\theta$ of the master equation (1.8):
--
--   1. $|\theta(t,x)|\le C_0$ on $[0,T]\times\mathbb R^d$;
--   2. the pair
--   $$h^\varpi_t=\frac1\varpi\theta(t,m_t),\qquad k^\varpi_t=\frac1\varpi\nabla_x\theta(t,m_t)$$
--   (read at $\min(t,T)$, i.e. frozen after $T$) solves the backward equation of (2.11) in the class of bounded processes;
--   3. every solution $(h',k')$ of the backward equation of (2.11) in that class satisfies, almost surely, $h'_t=\frac1\varpi\theta(t,m_t)$ for all $t\in[0,T]$, and $k'_t=\frac1\varpi\nabla_x\theta(t,m_t)$ for $dt\otimes d\mathbb P$-almost every $(t,\omega)$.
--
--   The identities (2.18) connect the probabilistic and the PDE representations of the equilibrium, and give existence and uniqueness of the limit system (2.11) of Theorem 2.4.
--
--   Differences from the source:
--   - encoding: (2.18) stated for the system (2.16) (h_t = θ_ε(t, m_t), k_t = ∇ₓθ_ε(t, m_t)) and transferred to (2.11) by (2.17) → stated directly for (2.11): h^ϖ = θ(·, m)/ϖ, k^ϖ = ∇ₓθ(·, m)/ϖ; reason: (2.17) h^ϖ = h/ϖ, k^ϖ = k/ϖ is a bijection between the two solution sets; (2.11) is the system of Theorem 2.4
--   - encoding: 'which holds true under both ℙ and ℙ^{h/ε}' → ℙ-almost surely; reason: ℙ and ℙ^{h/ε} are equivalent (positive density), so the null sets agree
--   - encoding: θ_ε, 'the solution to the PDE (1.8)' → every classical solution θ in the class IsClassicalSol; reason: the solution is unique in that class (milestone (1.8))
--   - reading: the solution classes are left implicit: hⁿ⁺¹ ∈ S^d(𝔽^W) (Lemma 2.1(ii)), kⁿ⁺¹ progressive; (2.11) solved 'in the class of bounded processes' (p.22) → scheme: m̄ⁿ, hⁿ adapted with continuous paths, (hⁿ⁺¹, kⁿ⁺¹) in L²_𝔽 (Peng1990.SMP.SolvesBSDE); limit: h^ϖ continuous with a deterministic a.s. bound, k^ϖ bounded dt⊗dℙ-a.e.; reason: the standard BSDE class for the scheme and the class in which p.22 asserts uniqueness for the limit
--   - encoding: time t ∈ [0, T], processes indexed by [0, T] → processes indexed by ℝ≥0, [0, T] cut out by t ≤ T; time integrals over [0, t] ⊂ ℝ; reason: Lean convention of the published Peng1990.SMP stochastic-calculus definitions; values after T never enter
--   - encoding: ℝᵈ with the Euclidean norm |·|; |·| on d × d matrices unnamed → Fin d → ℝ with |x|² = Σᵢ xᵢ² written explicitly; matrices carry the Frobenius norm; reason: Mathlib's default norm on Fin d → ℝ is the sup norm; all matrix norms are equivalent up to a factor depending only on d, which the constants absorb
--   - encoding: a constant depending only on d, T, ‖Q†f‖_{1,∞} and ‖R†g‖_{1,∞} → for every d ≥ 1, T > 0 and bounds L_f, L_g there is a constant valid for all Q, R, f, g with ‖Q†f‖_{1,∞} ≤ L_f and ‖R†g‖_{1,∞} ≤ L_g, all ε, ϖ and all data; reason: the uniform form of 'depends only on'; it is at least as strong as a function of the exact norms
--   - encoding: m₀ = 𝔼(X₀), with X₀, the idiosyncratic noise B and its intensity σ in the model → an arbitrary vector m₀ ∈ ℝᵈ; X₀, B and σ are not part of the data; reason: only 𝔼(X₀) enters (2.9)–(2.13); every m₀ ∈ ℝᵈ is 𝔼(X₀) for X₀ ≡ m₀
--   - encoding: the augmented filtration 𝔽^W of W on a complete probability space → augFiltration: the natural filtration of W (published Peng1990.SMP.brownianFiltration) joined with the σ-algebra of P-null sets, with P.IsComplete assumed; reason: on a complete space this is the usual augmentation
--   - encoding: the pair (θ_ε(t, m_t), ∇ₓθ_ε(t, m_t)), t ∈ [0, T] → the candidate pair read at min(t, T): equal to (θ(t, m_t)/ϖ, ∇ₓθ(t, m_t)/ϖ) on [0, T] and frozen after T; reason: θ is given only on [0, T] × ℝᵈ while the Lean processes are indexed by ℝ≥0 and must be continuous and progressive there; the values after T never enter (2.11)
-- source:
--   Delarue & Vasileiadis, Exploration Noise for Learning Linear-Quadratic Mean Field Games, arXiv:2107.00839v2 (https://arxiv.org/abs/2107.00839v2), §2.1.2, paragraph containing (2.18), p.22, with (2.17) p.22

import Mathlib
import Definitions.Def_ExploreLQMFG_Scheme
import Definitions.Def_ExploreLQMFG_Master

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Matrix

universe u

namespace ExploreLQMFG

/-- **The bounded solution of (2.11) and the identities (2.18)** (Delarue & Vasileiadis,
arXiv:2107.00839v2, §2.1.2, paragraph containing (2.18), p.22, with the change of variable
(2.17)).

Fix `d ≥ 1`, `T > 0` and bounds `L_f, L_g`. There is `C₀` such that, for all `Q, R`, all bounded
Lipschitz `f, g` with `‖Q†f‖_{1,∞} ≤ L_f`, `‖R†g‖_{1,∞} ≤ L_g`, all `ε ∈ (0, 1]`,
`ϖ ∈ (1, √2]`, every complete probability space carrying a `d`-dimensional Brownian motion `W`,
the Riccati solution `η` of (2.3), every `m₀ ∈ ℝᵈ`, every solution `m` of the forward equation
`dm_t = −η_t m_t dt + ε dW_t`, `m_0 = m₀`, and every classical solution `θ` of (1.8):

1. `|θ(t, x)| ≤ C₀` on `[0, T] × ℝᵈ` ("by a standard application of the maximum principle, θ_ε
   is bounded in terms of d, T, ‖Q†f‖_{1,∞} and ‖R†g‖_{1,∞}");
2. `h^ϖ_t := θ(t, m_t)/ϖ`, `k^ϖ_t := ∇ₓθ(t, m_t)/ϖ` solve the backward equation of (2.11) in the
   class of bounded processes (the identities (2.18) `h_t = θ_ε(t, m_t)`, `k_t = ∇ₓθ_ε(t, m_t)`
   for `h = ϖh^ϖ`, `k = ϖk^ϖ`, through (2.17));
3. every solution `(h', k')` of the backward equation of (2.11) in the class of bounded
   processes equals it: `h'_t = θ(t, m_t)/ϖ` for all `t ∈ [0, T]` almost surely, and
   `k'_t = ∇ₓθ(t, m_t)/ϖ` for `dt ⊗ dℙ`-a.e. `(t, ω) ∈ [0, T] × Ω`.

**Formalization Note.** The page states (2.18) for the system (2.16) and transfers to (2.11)
by (2.17); the milestone is stated directly on (2.11), the system of Theorem 2.4. The filtration
is the augmented Brownian filtration (`augFiltration`). `θ` is only given on `[0, T] × ℝᵈ`,
while the processes of the mission are indexed by `ℝ≥0` (and `IsLimitBdd` asks for continuous,
progressive paths on all of `ℝ≥0`), so the candidate pair of item 2 is read at `min(t, T)`: it
equals `(θ(t, m_t)/ϖ, ∇ₓθ(t, m_t)/ϖ)` on `[0, T]` and is frozen after `T`; the values of `θ`
for `t > T`, which `IsClassicalSol` leaves free, never enter. -/
theorem eq_2_18 {d : ℕ} (hd : 0 < d) (T : ℝ≥0) (hT : 0 < T) (Lf Lg : ℝ) :
    ∃ C₀ : ℝ, ∀ (Q R : Matrix (Fin d) (Fin d) ℝ) (f g : (Fin d → ℝ) → (Fin d → ℝ)),
      IsBddLip f → IsBddLip g → oneInfNorm (tmul Q f) ≤ Lf → oneInfNorm (tmul R g) ≤ Lg →
      ∀ ε ϖ : ℝ, 0 < ε → ε ≤ 1 → 1 < ϖ → ϖ ≤ Real.sqrt 2 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        [Measure.IsComplete P] (W : ℝ≥0 → Ω → Fin d → ℝ) (hW : Peng1990.SMP.IsStdBrownian P W)
        (η : ℝ → Matrix (Fin d) (Fin d) ℝ), IsRiccatiSol Q R T η →
      ∀ (m₀ : Fin d → ℝ) (m : ℝ≥0 → Ω → Fin d → ℝ), IsForwardLimit hW T η ε m₀ m →
      ∀ θ, IsClassicalSol T ε η (tmul Q f) (tmul R g) θ →
        (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, eNorm (θ t x) ≤ C₀) ∧
        IsLimitBdd hW T η (tmul Q f) (tmul R g) ε ϖ m
          (fun t ω => ϖ⁻¹ • θ (min (t : ℝ) T) (m (min t T) ω))
          (fun t ω => ϖ⁻¹ • gradMat θ (min (t : ℝ) T) (m (min t T) ω)) ∧
        ∀ (hϖ : ℝ≥0 → Ω → Fin d → ℝ) (kϖ : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ),
          IsLimitBdd hW T η (tmul Q f) (tmul R g) ε ϖ m hϖ kϖ →
          (∀ᵐ ω ∂P, ∀ t ≤ T, hϖ t ω = ϖ⁻¹ • θ t (m t ω)) ∧
          ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
            kϖ s.toNNReal ω = ϖ⁻¹ • gradMat θ s (m s.toNNReal ω) := by sorry

end ExploreLQMFG
