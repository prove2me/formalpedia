-- Prove2me | Theorems.Thm_CascadeCC_phi_decomposition
-- name    : CascadeCC.phi_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:34:44.672651+00:00
-- url     : https://prove2.me/theorems/3ebe95c2-4d28-4bef-bb5d-117d615fba70
-- title:
--   p.ec12 — $\mathbf E[R^{k,CC}(1,\tau^k-1)]=\Phi_1+\Phi_2$ and the reduction to the first $\tau-1$ periods (corrected: admissible threshold)
-- statement:
--   Let $a$ be a stationary optimal solution for $(T,y)$ with $\lambda>0$ and $a\in(0,u)^J$, $\varphi$ an admissible threshold, $\tau$ the stopping time of $\hat\varphi=\varphi/2$, and $(N,Y)$ scaled from $(T,y)$ by $k\ge1$. Then
--
--   $$
--   \mathbf E\bigl[R^{k,CC}(1,\tau-1)\bigr]=\mathbf E\Bigl[\sum_{t<\tau}\sum_j\sigma_j(\hat\alpha_t)r_j(\hat\alpha_{tj})\Bigr]
--   =\mathbf E\Bigl[\sum_{t<\tau}\sum_j(\sigma^D_j+\delta^\sigma_{tj})r_j(a_j+\epsilon_{tj})\Bigr]=\Phi_1+\Phi_2,
--   $$
--
--   and, with $\tilde V^D=\sum_j\sigma^D_jr_j(a_j)$,
--
--   $$
--   V^{k,D}-V^{k,CC}\le\mathbf E\Bigl[\sum_{t<\tau}\tilde V^D-R^{k,CC}(1,\tau-1)\Bigr]+(N-\mathbf E[\tau]+1)\tilde V^D .
--   $$
--
--   The first equality is the tower property, and the rest uses Lemma EC.2. The inequality throws away the revenue from period $\tau$ on.
--
--   **Formalization Note** $\sum_{t<\tau}\tilde V^D$ is $(\tau-1)\tilde V^D$.
--
--   Differences from the source:
--   - encoding: prices in Ω_p as actions, rates in Ω_α = [0, u] or (0, u] → rates in [0, u] as actions, with 0 the turn-off price and revenue 0; reason: A1 makes prices and rates equivalent and §4.2 does the same; S(y) and S^D(y) contain rate 0, and [0, u] covers both forms of Ω_α
--   - generalization: A1 (α_j twice differentiable) and A2 → not assumed; the instance carries only p_j, strictly decreasing with p_j(u) = 0, and A3 with strict concavity, the derivatives and the bound |r″_j| ≤ w required on (0, u] only; reason: A1 and A2 concern the price parametrization, and for Ω_α = [0, u] the conditions of A3 on (0, u] are implied by those on [0, u]; every instance of A1–A3 is an instance here
--   - reading: σ_j = σ_{j−1}(1 − α_j)ζ_j on pp.10, 14, but σ_{j+1} = σ_j(1 − α_j)ζ_j on pp.20, 24, Figure 1 and (EC.19) → σ_j(a) = λ∏_{i<j}(1 − a_i)ζ_i; reason: the source disagrees with itself; the form of pp.20, 24 is the one its analysis uses and the printed one has an index slip
--   - generalization: scaling factor k ≥ 1 with T^k = kT, y^k = ky → every real k ≥ 1 with N = kT and Y_j = k y_j natural numbers, y real-valued; reason: it contains k ∈ ℕ with y ∈ ℕ^J, and the fractional y_j of the proof's T = 1 reduction
--   - encoding: standing setting of the proof, a^D ∈ [L, U]^J and Lemma 5 → hypotheses 0 < λ and a_j ∈ (0, u); reason: the printed choice of φ > 0 presupposes them; they follow from Theorem 3's hypotheses at λ > 0, and the goal keeps no such hypothesis
--   - correction: φ > 0 largest with (EC.32)–(EC.35) → IsAdmissible: 0 < φ, φ ≤ v^D_j, Qφ ≤ σ^D_j, (1 + Q)φ ≤ σ^D_j(u − a_j); reason: (EC.34) forces φ = 0 at σ^D_1 = λ = 1, and Q⁻¹ is undefined at J = 1, so that as printed the threshold can be vacuous, on the instance of the paper's own Figures 2–3 with λ = 1; (EC.35) gives α̂ < 1 and not α̂ ≤ u
--   - encoding: the conditional formulas of §7.3 with T = 1 → general (N, Y), with τ and sums over periods t = s + 1 < τ, and the expectation the finite sum over outcome paths; reason: this is the path law of the model; no reduction to T = 1 is used
-- source:
--   Najafi, Duenyas, Jasin, Uichanco, Multi-product Dynamic Pricing with Limited Inventories under a Cascade Click Model, SSRN abstract_id=3362921, p.ec12; first display of Step 3, p.ec11

import Mathlib
import Definitions.Def_CascadeCC_Analysis

namespace CascadeCC

variable {J : ℕ}

/-- p.ec12 and the first display of Step 3, p.ec11 (SSRN abstract_id=3362921): the loss is bounded by the loss
before τ plus the remaining periods, and E[R^{k,CC}(1, τ − 1)] = E[∑_{t<τ} ∑_j σ_j(α̂_t) r_j(α̂_tj)]
= E[∑_{t<τ} ∑_j (σ^D_j + δ^σ_tj) r_j(a_j + ϵ_tj)] = Φ₁ + Φ₂.

**Formalization Note** The threshold is φ̂ = φ/2. The first equality is the tower property combined with
`lemma_EC2`. The sums run over periods t = s + 1 < τ. -/
theorem phi_decomposition (M : Instance J) (T : ℕ) (hT : 0 < T) (y : Fin J → ℝ) (hy : ∀ j, 0 ≤ y j)
    (a : Fin J → ℝ) (ha : IsStationaryOptimal M T y a) (hlam : 0 < M.lam)
    (hau : ∀ j, a j ∈ Set.Ioo 0 M.u) (φ : ℝ) (hφ : IsAdmissible M a φ)
    (k : ℝ) (hk : 1 ≤ k) (N : ℕ) (Y : Fin J → ℕ) (hN : (N : ℝ) = k * T)
    (hY : ∀ j, (Y j : ℝ) = k * y j) :
    ccExpect M N Y a (stoppedRevenue M N Y a (φ / 2)) =
        ccExpect M N Y a (fun ω => sumBeforeTau M N Y a (φ / 2) ω fun s =>
          ∑ j, arrival M (hatRate M a (delta M N Y a ω s)) j *
            M.r j (hatRate M a (delta M N Y a ω s) j)) ∧
      ccExpect M N Y a (fun ω => sumBeforeTau M N Y a (φ / 2) ω fun s =>
          ∑ j, arrival M (hatRate M a (delta M N Y a ω s)) j *
            M.r j (hatRate M a (delta M N Y a ω s) j)) =
        ccExpect M N Y a (fun ω => sumBeforeTau M N Y a (φ / 2) ω fun s =>
          ∑ j, (arrival M a j + arrivalDev M a (delta M N Y a ω s) j) *
            M.r j (a j + rateDev M a (delta M N Y a ω s) j)) ∧
      ccExpect M N Y a (stoppedRevenue M N Y a (φ / 2)) =
        Phi1 M N Y a (φ / 2) + Phi2 M N Y a (φ / 2) ∧
      detValue M N (fun j => (Y j : ℝ)) - ccValue M N Y a ≤
        ccExpect M N Y a (fun ω => ((tau M N Y a (φ / 2) ω : ℝ) - 1) * statObjective M a -
            stoppedRevenue M N Y a (φ / 2) ω) +
          ((N : ℝ) - ccExpect M N Y a (fun ω => (tau M N Y a (φ / 2) ω : ℝ)) + 1) *
            statObjective M a := by sorry

end CascadeCC
