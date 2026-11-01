-- Prove2me | Theorems.Thm_CascadeCC_theorem_3_cc_log_loss
-- name    : CascadeCC.theorem_3_cc_log_loss
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:35:25.43878+00:00
-- url     : https://prove2.me/theorems/99fb9fe3-8047-4400-8ca4-c24e7a64c361
-- title:
--   Theorem 3 — the Cascade Correction policy loses $O(\log k)$ against the deterministic benchmark
-- statement:
--   Consider the Cascade Click model, with horizon $T\ge1$ and inventory $y\ge0$. Let $a^D$ be a stationary optimal solution of DET, and suppose that $a^D\in[L,U]^J$ for some $0<L<U<1$ and that $|r_j'|$ is uniformly bounded on $[L,U]$. Then there is $\Psi_2>0$, independent of $k$, such that for every $k\ge1$ for which $N=kT$ and $Y_j=ky_j$ are natural numbers,
--
--   $$
--   V^{k,D}-V^{k,CC}\ \le\ \Psi_2\,(1+\log k).
--   $$
--
--   Here $V^{k,D}$ is the optimal value of DET for horizon $N$ and inventory $Y$, and $V^{k,CC}$ is the expected total revenue of the Cascade Correction policy, under its own path law, with the correction weights of horizon $N$.
--
--   Since $V^{k,D}$ grows linearly in $k$, the policy's relative loss vanishes at rate $O(\log k/k)$, while it solves DET once and only solves a linear system in each period.
--
--   **Formalization Note** $\Psi_2$ may depend on the instance, $T$, $y$, $a^D$, $L$, $U$, and the bound on $r'$, never on $k$, $N$, $Y$. Binding inventory constraints are not assumed. Theorem 3 does not exclude $\lambda=0$, where both values are $0$.
--
--   Differences from the source:
--   - encoding: prices in Ω_p as actions, rates in Ω_α = [0, u] or (0, u] → rates in [0, u] as actions, with 0 the turn-off price and revenue 0; reason: A1 makes prices and rates equivalent and §4.2 does the same; S(y) and S^D(y) contain rate 0, and [0, u] covers both forms of Ω_α
--   - generalization: A1 (α_j twice differentiable) and A2 → not assumed; the instance carries only p_j, strictly decreasing with p_j(u) = 0, and A3 with strict concavity, the derivatives and the bound |r″_j| ≤ w required on (0, u] only; reason: A1 and A2 concern the price parametrization, and for Ω_α = [0, u] the conditions of A3 on (0, u] are implied by those on [0, u]; every instance of A1–A3 is an instance here
--   - reading: σ_j = σ_{j−1}(1 − α_j)ζ_j on pp.10, 14, but σ_{j+1} = σ_j(1 − α_j)ζ_j on pp.20, 24, Figure 1 and (EC.19) → σ_j(a) = λ∏_{i<j}(1 − a_i)ζ_i; reason: the source disagrees with itself; the form of pp.20, 24 is the one its analysis uses and the printed one has an index slip
--   - generalization: scaling factor k ≥ 1 with T^k = kT, y^k = ky → every real k ≥ 1 with N = kT and Y_j = k y_j natural numbers, y real-valued; reason: it contains k ∈ ℕ with y ∈ ℕ^J, and the fractional y_j of the proof's T = 1 reduction
--   - reading: |r_j'| uniformly bounded on [L, U] → the bound on [L, U] ∩ (0, u]; reason: r_j' is defined on Ω_α only; for U ≤ u this is all of [L, U]
--   - reading: '0 < L < U < 1 (i.e., a^D_j lies in a strict interior of Ω_α)' → the literal hypothesis U < 1; reason: for u < 1 it does not by itself say a^D_j < u, and Lemma 5 supplies that, so the literal reading is the stronger theorem
--   - encoding: V^{k,D}, the optimal value (max) of DET, and V^{k,CC} = E[∑_t ∑_j p_tj D_tj] → detValue, a supremum, and ccValue, the finite sum over outcome paths under the policy's own path law; reason: the supremum is attained at the scaled stationary solution (scaled_value), and the period outcomes take finitely many values
-- source:
--   Najafi, Duenyas, Jasin, Uichanco, Multi-product Dynamic Pricing with Limited Inventories under a Cascade Click Model, SSRN abstract_id=3362921, Theorem 3, p.25

import Mathlib
import Definitions.Def_CascadeCC_Analysis

namespace CascadeCC

variable {J : ℕ}

/-- Theorem 3, p.25 (SSRN abstract_id=3362921): if a^D ∈ [L, U]^J for some 0 < L < U < 1 and |r_j'| are uniformly
bounded on [L, U], then there exists Ψ₂ > 0 independent of k ≥ 1 such that V^{k,D} − V^{k,CC} ≤ Ψ₂(1 + log k).

**Formalization Note** The scaling factor is real, with kT and k y_j integers; this contains k ∈ ℕ with
y ∈ ℕ^J. V^{k,D} is the supremum `detValue` for horizon N = kT and inventory Y = ky, V^{k,CC} the expected
realized revenue under the policy's own law. The bound on r' is required on [L, U] ∩ (0, u], where r' is
defined. The literal `U < 1` is kept. -/
theorem theorem_3_cc_log_loss (M : Instance J) (T : ℕ) (hT : 0 < T) (y : Fin J → ℝ)
    (hy : ∀ j, 0 ≤ y j) (a : Fin J → ℝ) (ha : IsStationaryOptimal M T y a) (L U C : ℝ)
    (hL : 0 < L) (hLU : L < U) (hU : U < 1) (haLU : ∀ j, a j ∈ Set.Icc L U)
    (hr' : ∀ j, ∀ x ∈ Set.Icc L U ∩ Set.Ioc 0 M.u, |M.r' j x| ≤ C) :
    ∃ Ψ₂ : ℝ, 0 < Ψ₂ ∧ ∀ (k : ℝ), 1 ≤ k → ∀ (N : ℕ) (Y : Fin J → ℕ),
      (N : ℝ) = k * T → (∀ j, (Y j : ℝ) = k * y j) →
      detValue M N (fun j => (Y j : ℝ)) - ccValue M N Y a ≤ Ψ₂ * (1 + Real.log k) := by sorry

end CascadeCC
