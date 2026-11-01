-- Prove2me | Theorems.Thm_CascadeCC_phi2_bound
-- name    : CascadeCC.phi2_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:35:28.996187+00:00
-- url     : https://prove2.me/theorems/4d7a7e2a-f304-44ff-b28e-31463a41822c
-- title:
--   p.ec13 — $\Phi_2\ge-O(\log k)$ (corrected: admissible threshold)
-- statement:
--   Under the standing hypotheses of the analysis (a stationary optimal $a\in(0,u)^J$ for $(T,y)$, $\lambda>0$, an admissible threshold $\varphi$), there is $C>0$ such that for every $k\ge1$ and every $(N,Y)$ scaled from $(T,y)$ by $k$,
--
--   $$
--   \Phi_2\ \ge\ -C(1+\log N),
--   $$
--
--   with $\tau$ the stopping time of $\hat\varphi=\varphi/2$.
--
--   With Observation 6 this bounds the expected loss during the first $\tau-1$ periods.
--
--   Differences from the source:
--   - encoding: prices in Ω_p as actions, rates in Ω_α = [0, u] or (0, u] → rates in [0, u] as actions, with 0 the turn-off price and revenue 0; reason: A1 makes prices and rates equivalent and §4.2 does the same; S(y) and S^D(y) contain rate 0, and [0, u] covers both forms of Ω_α
--   - generalization: A1 (α_j twice differentiable) and A2 → not assumed; the instance carries only p_j, strictly decreasing with p_j(u) = 0, and A3 with strict concavity, the derivatives and the bound |r″_j| ≤ w required on (0, u] only; reason: A1 and A2 concern the price parametrization, and for Ω_α = [0, u] the conditions of A3 on (0, u] are implied by those on [0, u]; every instance of A1–A3 is an instance here
--   - reading: σ_j = σ_{j−1}(1 − α_j)ζ_j on pp.10, 14, but σ_{j+1} = σ_j(1 − α_j)ζ_j on pp.20, 24, Figure 1 and (EC.19) → σ_j(a) = λ∏_{i<j}(1 − a_i)ζ_i; reason: the source disagrees with itself; the form of pp.20, 24 is the one its analysis uses and the printed one has an index slip
--   - generalization: scaling factor k ≥ 1 with T^k = kT, y^k = ky → every real k ≥ 1 with N = kT and Y_j = k y_j natural numbers, y real-valued; reason: it contains k ∈ ℕ with y ∈ ℕ^J, and the fractional y_j of the proof's T = 1 reduction
--   - encoding: standing setting of the proof, a^D ∈ [L, U]^J and Lemma 5 → hypotheses 0 < λ and a_j ∈ (0, u); reason: the printed choice of φ > 0 presupposes them; they follow from Theorem 3's hypotheses at λ > 0, and the goal keeps no such hypothesis
--   - correction: φ > 0 largest with (EC.32)–(EC.35) → IsAdmissible: 0 < φ, φ ≤ v^D_j, Qφ ≤ σ^D_j, (1 + Q)φ ≤ σ^D_j(u − a_j); reason: (EC.34) forces φ = 0 at σ^D_1 = λ = 1, and Q⁻¹ is undefined at J = 1, so that as printed the threshold can be vacuous, on the instance of the paper's own Figures 2–3 with λ = 1; (EC.35) gives α̂ < 1 and not α̂ ≤ u
--   - encoding: O(log k) → an explicit constant: ∃ C > 0, ∀ scaled (N, Y), a bound C(1 + log N); reason: a bound in log N is one in log k since N = kT, and C may depend on T
--   - encoding: the conditional formulas of §7.3 with T = 1 → general (N, Y), with τ and sums over periods t = s + 1 < τ, and the expectation the finite sum over outcome paths; reason: this is the path law of the model; no reduction to T = 1 is used
--   - generalization: |r′_j| uniformly bounded on [L, U] (Theorem 3's hypothesis, carried into Step 3) → not assumed; reason: A3's bound |r″_j| ≤ w on (0, u] gives |r′_j(x)| ≤ |r′_j(a_j)| + w·u there, so the hypothesis is implied
-- source:
--   Najafi, Duenyas, Jasin, Uichanco, Multi-product Dynamic Pricing with Limited Inventories under a Cascade Click Model, SSRN abstract_id=3362921, p.ec13

import Mathlib
import Definitions.Def_CascadeCC_Analysis

namespace CascadeCC

variable {J : ℕ}

/-- p.ec13 (SSRN abstract_id=3362921): Φ₂ ≥ −O(log k).

**Formalization Note** O(log k) is an explicit constant: ∃ C, for all scaled (N, Y), with the bound
C(1 + log N). The threshold is φ̂ = φ/2. The constant may depend on T. -/
theorem phi2_bound (M : Instance J) (T : ℕ) (hT : 0 < T) (y : Fin J → ℝ) (hy : ∀ j, 0 ≤ y j)
    (a : Fin J → ℝ) (ha : IsStationaryOptimal M T y a) (hlam : 0 < M.lam)
    (hau : ∀ j, a j ∈ Set.Ioo 0 M.u) (φ : ℝ) (hφ : IsAdmissible M a φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℝ), 1 ≤ k → ∀ (N : ℕ) (Y : Fin J → ℕ),
      (N : ℝ) = k * T → (∀ j, (Y j : ℝ) = k * y j) →
      -(C * (1 + Real.log N)) ≤ Phi2 M N Y a (φ / 2) := by sorry

end CascadeCC
