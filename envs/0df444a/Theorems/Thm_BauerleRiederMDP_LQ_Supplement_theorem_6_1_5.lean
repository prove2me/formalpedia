-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_6_1_5
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_6_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T23:56:06.930854+00:00
-- url     : https://prove2.me/theorems/8f57e327-8c9e-5097-b1fb-e998b70d5a21
-- title:
--   Theorem 6.1.5 (corrected: n ≥ 1) — partial observation versus known up-probability: comparison of the invested fractions
-- statement:
--   For all $n$ and $\rho  \in  D_{Q_0}$ it holds: $\alpha ^*_n(\rho ) \ge  \alpha ^*_n(\bar{\rho})$ if $0 < \gamma  < 1$ and $\alpha ^*_n(\rho ) \le  \alpha ^*_n(\bar{\rho})$ if $\gamma  < 0$. Here $\alpha ^*_n(\rho )$ is the optimal fraction invested in the stock, the maximum point of (6.4), and $\alpha ^*_n(\bar{\rho})$ is the complete-observation case $\rho  = \delta _{\bar{\rho}}$, $\bar{\rho} = \int  \theta  \rho (d\theta )$.
--
--   **Formalization Note.** $\alpha ^*_n$ is a maximum point over $[0, 1]$ of $\alpha  \mapsto  obj(d_{n-1}, \rho , \alpha )$, the objective of (6.4) with the continuation values $d_{n-1}$ of (6.4); it exists for $n \ge  1$ stages to go, correcting the book's index slip "$n \in  \mathbb N _0$" (for $n = 0$ there is no decision). The statement is made for every maximum point (the maximum point is unique since $d < 1 + i < u$). $\rho $ ranges over the posteriors $\hat{\mu}(\cdot |m, k)$, $m \le  k$, of an arbitrary prior $Q_0$ on $(0, 1)$.
--
--   Differences from the source:
--   - correction: for all n ∈ ℕ_0 → for all n ≥ 1 stages to go; reason: α*_n, the maximum point of (6.4), is undefined at n = 0 because (6.4) uses d_{n−1}; n ∈ ℕ_0 is an index slip
--   - encoding: measures on Θ = (0,1) → measures on ℝ carried by (0,1); reason: so that the point mass δ_{ρ̄} is available; same instances
--   - reading: α*_n(ρ) the solution of (6.4) → every maximum point over [0,1]; reason: the maximum point is unique since d < 1+i < u
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 6.1.5, p.180 (PDF 193)

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BinomBayes
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BinomBayes_Phi
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BinomBayes_obj
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BinomBayes_dSeq
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BinomBayes_posterior

open MeasureTheory

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem 6.1.5** (corrected index range) (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), Theorem 6.1.5, p.180, PDF 193, binomial model of pp.178–179,
PDF 191–192). For all `n` and `ρ ∈ D_{Q_0}` it holds: `α*_n(ρ) ≥ α*_n(ρ̄)` if `0 < γ < 1` and
`α*_n(ρ) ≤ α*_n(ρ̄)` if `γ < 0`. Here `α*_n(ρ)` is the optimal fraction invested in the stock, the
maximum point of (6.4), and `α*_n(ρ̄)` is the complete-observation case `ρ = δ_{ρ̄}`,
`ρ̄ = ∫ θ ρ(dθ)`.

**Formalization Note.** `α*_n` is a maximum point over `[0, 1]` of `α ↦ obj(d_{n−1}, ρ, α)`, the
objective of (6.4) with the continuation values `d_{n−1}` of (6.4); it exists for `n ≥ 1` stages to
go, correcting the book's index slip "`n ∈ ℕ_0`" (for `n = 0` there is no decision). The statement
is made for every maximum point (the maximum point is unique since `d < 1 + i < u`). `ρ` ranges
over the posteriors `μ̂(·|m, k)`, `m ≤ k`, of an arbitrary prior `Q_0` on `(0, 1)`. -/
theorem theorem_6_1_5 (B : BinomBayes) (n : ℕ) (hn : 1 ≤ n) (m k : ℕ) (hmk : m ≤ k)
    (α α' : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα' : α' ∈ Set.Icc (0 : ℝ) 1)
    (hmax : ∀ a ∈ Set.Icc (0 : ℝ) 1,
      B.obj (B.dSeq (n - 1)) (B.posterior m k) a ≤ B.obj (B.dSeq (n - 1)) (B.posterior m k) α)
    (hmax' : ∀ a ∈ Set.Icc (0 : ℝ) 1,
      B.obj (B.dSeq (n - 1)) (Measure.dirac (∫ θ, θ ∂B.posterior m k)) a ≤
        B.obj (B.dSeq (n - 1)) (Measure.dirac (∫ θ, θ ∂B.posterior m k)) α') :
    (0 < B.γ → α' ≤ α) ∧ (B.γ < 0 → α ≤ α') := by sorry

end BauerleRiederMDP.LQ.Supplement
