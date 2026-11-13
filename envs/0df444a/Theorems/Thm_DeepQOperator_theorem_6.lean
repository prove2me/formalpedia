-- Prove2me | Theorems.Thm_DeepQOperator_theorem_6
-- name    : DeepQOperator.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:03:30.557963+00:00
-- url     : https://prove2.me/theorems/dcb22564-80c9-400f-bf7e-bd6729c0d6d3
-- title:
--   Theorem 6: the decision-boundary spectral lower bound for randomized fixed affine designs
-- statement:
--   Let $P\subset\mathbb R^d$ be compact and let two decisions have continuous contrast $g=t_+-t_-$. Let $X$ have a $C^1$ compactly supported density $\rho$ and finite positive-definite score matrix $I=\mathbb E[\nabla\log\rho(X)\nabla\log\rho(X)^{\mathsf T}]$. Suppose finitely many labels $l$, with probabilities $p_l$, have centers $x_l$, normals $n_l$, directions $v_l$, and positive $R_l$, $c_l$ such that
--   $$n_l^{\mathsf T}v_l=1,\qquad |n_l^{\mathsf T}X|\le R_l\ \text{on }\operatorname{supp}\rho,\tag{21}$$
--   $K_l:=x_l+\operatorname{supp}\rho+[-R_l,R_l]v_l\subset P$, and $g(x)=c_ln_l^{\mathsf T}(x-x_l)$ for every $x\in K_l$. Set
--   $$B=I^{-1/2}\Big(\sum_l\frac{p_lc_l}{4R_l}n_ln_l^{\mathsf T}\Big)I^{-1/2},\qquad\lambda_1\ge\dots\ge\lambda_d\ge0\tag{22}$$
--   for its ordered eigenvalues. Then every randomized fixed design of at most $N$ arbitrary affine measurements has worst expected regret at least
--   $$\sum_{k>N}\lambda_k.\tag{23}$$
--   The empty tail is zero, and no computational restriction is placed on the decoder.
--
--   Applied to the prior of Appendix D.4, this gives (10) and, through the reply simulations, the lower bounds (7).
--
--   **Formalization Note** $\operatorname{supp}\rho$ is the closed support. The loss is $\max(0,-g)$ for $+$ and $\max(0,g)$ for $-$. Designs have $N$ rows (zero rows allowed), a standard Borel probability seed space, and are measurable.
--
--   Differences from the source:
--   - encoding: 𝔥^{…}_B, the infimum over protocols of sup_θ E_ω ℓ → every protocol of the class satisfies bound ≤ ⨆_{θ ∈ P_cb} ∫⁻ ω, ofReal ℓ(A(θ;ω), θ) dμ; reason: an infimum is ≥ a bound iff every member is; the supremum need not be attained
--   - encoding: randomness on a standard Borel space → seed space Ω : Type with [StandardBorelSpace Ω] and a probability measure; the protocol is measurable in the seed, quantizers jointly measurable; reason: §5 p.8; every standard Borel space is Borel isomorphic to a Borel subset of ℝ, so Ω : Type omits none
--   - encoding: I^{−1/2} → a positive definite S with S * S = I⁻¹; reason: the positive definite square root is unique
--   - encoding: "probabilities p_l" of finitely many labels → a finite type of labels, p_l ≥ 0, Σ p_l = 1; reason: definition of a probability vector
--   - encoding: λ_1 ≥ ⋯ ≥ λ_d, tail k > N → eigenvalues₀ indexed from 0, tail N ≤ k; reason: index shift by one
--   - encoding: "at most N" measurements → exactly N rows, zero rows allowed; reason: a zero row is a constant
--   - encoding: "continuous contrast" g on P → g continuous on P; reason: g is only evaluated on P
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), §5, Theorem 6, eqs. (21)–(23), p.8 (PDF p.11)

import Mathlib
import Definitions.Def_DeepQOperator_ExactDesign
import Definitions.Def_DeepQOperator_ScoreMatrix

open MeasureTheory Matrix

namespace DeepQOperator

/-- **Theorem 6 (Decision-boundary spectral lower bound)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), §5, p.8, PDF p.11).

Let `P ⊂ ℝ^d` be compact and let two decisions have continuous contrast `g = t₊ - t₋`. Let `X` have a
`C¹` compactly supported density `ρ` and finite positive-definite score matrix
`I = E[∇log ρ(X)∇log ρ(X)ᵀ]`. Suppose finitely many labels `l`, with probabilities `p_l`, have centers
`x_l`, normals `n_l`, directions `v_l`, and positive `R_l`, `c_l` such that `n_lᵀv_l = 1`,
`|n_lᵀX| ≤ R_l` on `supp ρ` (21), `K_l := x_l + supp ρ + [-R_l, R_l]v_l ⊂ P`, and
`g(x) = c_l n_lᵀ(x - x_l)` for every `x ∈ K_l`. Set
`B = I^{-1/2}(Σ_l (p_l c_l/(4R_l)) n_l n_lᵀ)I^{-1/2}` (22) with ordered eigenvalues
`λ₁ ≥ ⋯ ≥ λ_d ≥ 0`. Every randomized fixed design of at most `N` arbitrary affine measurements has worst
expected regret at least `Σ_{k>N} λ_k` (23). The empty tail is zero.

**Formalization Note.** `supp ρ` is `tsupport ρ`. The loss of the binary decision is `binLoss g`
(`max(0, -g)` for `+`, `max(0, g)` for `-`), which is (3). The probabilities are `p_l ≥ 0` with
`Σ p_l = 1`. `I^{-1/2}` is the positive definite `S` with `S * S = I⁻¹`. "At most `N`" is `N` rows with
zero rows allowed; the seed space is any standard Borel probability space and the design is measurable.
Eigenvalues are 0-indexed (`eigenvalues₀`), so the tail `k > N` is `N ≤ k.val`. -/
theorem theorem_6 {d : ℕ} (Pset : Set (Fin d → ℝ)) (hP : IsCompact Pset)
    (g : (Fin d → ℝ) → ℝ) (hg : ContinuousOn g Pset)
    (ρ : (Fin d → ℝ) → ℝ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ContDiff ℝ 1 ρ) (hρK : HasCompactSupport ρ)
    (hρ1 : ∫ x, ρ x = 1) (hI : FiniteFisher ρ) (hIpd : (fisherMatrix ρ).PosDef)
    {L : Type} [Fintype L] (p : L → ℝ) (hp0 : ∀ l, 0 ≤ p l) (hp1 : ∑ l, p l = 1)
    (xc nv vv : L → Fin d → ℝ) (R c : L → ℝ) (hR : ∀ l, 0 < R l) (hc : ∀ l, 0 < c l)
    (h21a : ∀ l, nv l ⬝ᵥ vv l = 1) (h21b : ∀ l, ∀ x ∈ tsupport ρ, |nv l ⬝ᵥ x| ≤ R l)
    (hK : ∀ l, ∀ y ∈ tsupport ρ, ∀ t ∈ Set.Icc (-R l) (R l), xc l + y + t • vv l ∈ Pset)
    (hgK : ∀ l, ∀ y ∈ tsupport ρ, ∀ t ∈ Set.Icc (-R l) (R l),
      g (xc l + y + t • vv l) = c l * (nv l ⬝ᵥ (xc l + y + t • vv l - xc l)))
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef) (hSS : S * S = (fisherMatrix ρ)⁻¹)
    (N : ℕ) (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (D : ExactDesign (Fin d) Ω N) (hD : D.IsMeasurable) :
    ENNReal.ofReal (∑ k ∈ Finset.univ.filter (fun k : Fin (Fintype.card (Fin d)) => N ≤ k.val),
        (boundaryMatrix_isHermitian hS.isHermitian p c R nv).eigenvalues₀ k) ≤
      designRegret Pset (binLoss g) μ D := by sorry

end DeepQOperator
