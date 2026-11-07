-- Prove2me | Theorems.Thm_EulerSparsify_proposition_3_9
-- name    : EulerSparsify.proposition_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:31:47.522952+00:00
-- url     : https://prove2.me/theorems/5ae4fc5a-d080-4f81-9356-eb2b7af6a630
-- title:
--   Proposition 3.9 — matrix small-ball theorem: $\gamma(\{x:\|\sum_ix_iA_i\|\le4\sigma\})\ge e^{-C_{AS}n}$ [AS26]
-- statement:
--   There is a constant $C_{\mathrm{AS}}>0$ such that the following holds for all $n,m\in\mathbb N$ and $\sigma\ge0$. Let $A_1,\dots,A_m$ be real symmetric $n\times n$ matrices with
--
--   $$\sum_{i=1}^mA_i^2\preceq\sigma^2I,$$
--
--   and let $\mathcal K=\bigl\{x\in\mathbb R^m:\ \bigl\|\sum_{i=1}^mx_iA_i\bigr\|_{\mathrm{op}}\le4\sigma\bigr\}$. Then the standard Gaussian measure of $\mathcal K$ satisfies
--
--   $$\gamma_m(\mathcal K)\ge\exp(-C_{\mathrm{AS}}\,n).$$
--
--   The convex body of signings with small matrix discrepancy has large Gaussian measure; with Proposition 3.10 this gives the matrix partial colouring of Algorithm 5.1. The result is Theorem 1.4 of Akbas–Sra, *A Proof of the Matrix Spencer Conjecture* (arXiv:2608.28816), cited by the paper.
--
--   Differences from the source:
--   - reading: header "with σ = 1 and d = n" and the body's σ → every σ ≥ 0; reason: the body keeps σ (hypothesis ≼ σ²I, radius 4σ); σ = 1 is the special case and the general case follows by scaling; σ < 0 would make 𝒦 empty
--   - reading: ‖Σ A_i²‖_op ≼ σ²I → Σ A_i² ≼ σ²I (Loewner); reason: the printed relation mixes a norm and a Loewner bound; both readings agree because Σ A_i² is PSD
--   - encoding: 𝕊ⁿ, ‖·‖ in 𝒦, γ → real symmetric n×n matrices, spectral norm opNorm, standard Gaussian on EuclideanSpace ℝ (Fin m); reason: §3 conventions
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Proposition 3.9 ([AS26], Theorem 1.4), p.11 (PDF p.13)

import Mathlib
import Definitions.Def_LiqPremiaEq_opNorm

namespace EulerSparsify

open MeasureTheory ProbabilityTheory

/-- **Proposition 3.9** ([AS26], Theorem 1.4; matrix small-ball theorem), p.11, PDF p.13.
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Proposition 3.9: "([AS26], Theorem 1.4 with σ = 1 and d = n). There is a constant C_AS > 0
such that, for any {A_i}_{i∈[m]} ⊂ 𝕊ⁿ satisfying ‖Σ_{i=1}^m A_i²‖_op ≼ σ²I and letting
𝒦 := {x ∈ ℝ^m : ‖Σ_{i=1}^m x_i A_i‖ ≤ 4σ} it satisfies that γ(𝒦) ≥ exp(−C_AS n)."
[AS26] is Akbas–Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816.

**Formalization Note.** `𝕊ⁿ` is the real symmetric `n × n` matrices; the hypothesis is the Loewner
bound `Σ A_i² ≼ σ²I` (equivalent to `‖Σ A_i²‖_op ≤ σ²` since `Σ A_i²` is PSD); the norm in `𝒦` is
the spectral norm `LiqPremiaEq.opNorm`; `γ = γ_m` is the standard Gaussian measure on `ℝ^m`. Stated for every
`σ ≥ 0`, as the body of the statement keeps `σ` (`σ = 1` is the case of the header). `C_AS` comes
before `n`, `m`, `σ` and the matrices. -/
theorem proposition_3_9 :
    ∃ C_AS : ℝ, 0 < C_AS ∧
      ∀ (n m : ℕ) (σ : ℝ), 0 ≤ σ → ∀ A : Fin m → Matrix (Fin n) (Fin n) ℝ,
        (∀ i, (A i).IsSymm) →
        (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ) - ∑ i, A i * A i).PosSemidef →
        ENNReal.ofReal (Real.exp (-(C_AS * n))) ≤
          stdGaussian (EuclideanSpace ℝ (Fin m))
            {x | LiqPremiaEq.opNorm (∑ i, x i • A i) ≤ 4 * σ} := by sorry

end EulerSparsify
