-- Prove2me | Theorems.Thm_CascadeCC_lemma_EC2
-- name    : CascadeCC.lemma_EC2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:34:31.614749+00:00
-- url     : https://prove2.me/theorems/cbb9dbed-f461-4176-9138-3de245d04896
-- title:
--   Lemma EC.2 — below the threshold the policy follows the ideal path (corrected: admissible threshold, general inventories)
-- statement:
--   Let $a$ be a stationary optimal solution for $(T,y)$ with $\lambda>0$ and $a\in(0,u)^J$, let $\varphi$ be an admissible threshold, $\hat\varphi=\varphi/2$, and let $(N,Y)$ scale $(T,y)$ by $k\ge1$. For a period $t\le N$ write
--
--   $$
--   \hat y_{tj}=Y_j-(t-1)v^D_j-(N-t+1)\delta^v_{tj}.
--   $$
--
--   Suppose $\alpha_s=\hat\alpha_s$ and $y_s=\hat y_s$ for all $s\le t-1$. If $\|\delta^v_t\|_\infty<\hat\varphi$, then $\alpha_t=\hat\alpha_t$ and $y_t=\hat y_t$. Moreover $\hat\alpha_{tj}\in(0,u)$ and $y_{tj}>0$ for all $j$.
--
--   Iterating this, as long as the correction stays below the threshold, the policy applies its ideal rates, is never out of stock, and has an exact inventory formula.
--
--   **Formalization Note** The statement is pathwise, for a history before period $t$. The premises also say that $\hat\alpha_s$ is defined and that every sale in the history has stock to sell, which holds on every path of positive probability.
--
--   Differences from the source:
--   - encoding: prices in Ω_p as actions, rates in Ω_α = [0, u] or (0, u] → rates in [0, u] as actions, with 0 the turn-off price and revenue 0; reason: A1 makes prices and rates equivalent and §4.2 does the same; S(y) and S^D(y) contain rate 0, and [0, u] covers both forms of Ω_α
--   - generalization: A1 (α_j twice differentiable) and A2 → not assumed; the instance carries only p_j, strictly decreasing with p_j(u) = 0, and A3 with strict concavity, the derivatives and the bound |r″_j| ≤ w required on (0, u] only; reason: A1 and A2 concern the price parametrization, and for Ω_α = [0, u] the conditions of A3 on (0, u] are implied by those on [0, u]; every instance of A1–A3 is an instance here
--   - reading: σ_j = σ_{j−1}(1 − α_j)ζ_j on pp.10, 14, but σ_{j+1} = σ_j(1 − α_j)ζ_j on pp.20, 24, Figure 1 and (EC.19) → σ_j(a) = λ∏_{i<j}(1 − a_i)ζ_i; reason: the source disagrees with itself; the form of pp.20, 24 is the one its analysis uses and the printed one has an index slip
--   - generalization: scaling factor k ≥ 1 with T^k = kT, y^k = ky → every real k ≥ 1 with N = kT and Y_j = k y_j natural numbers, y real-valued; reason: it contains k ∈ ℕ with y ∈ ℕ^J, and the fractional y_j of the proof's T = 1 reduction
--   - encoding: standing setting of the proof, a^D ∈ [L, U]^J and Lemma 5 → hypotheses 0 < λ and a_j ∈ (0, u); reason: the printed choice of φ > 0 presupposes them; they follow from Theorem 3's hypotheses at λ > 0, and the goal keeps no such hypothesis
--   - correction: φ > 0 largest with (EC.32)–(EC.35) → IsAdmissible: 0 < φ, φ ≤ v^D_j, Qφ ≤ σ^D_j, (1 + Q)φ ≤ σ^D_j(u − a_j); reason: (EC.34) forces φ = 0 at σ^D_1 = λ = 1, and Q⁻¹ is undefined at J = 1, so that as printed the threshold can be vacuous, on the instance of the paper's own Figures 2–3 with λ = 1; (EC.35) gives α̂ < 1 and not α̂ ≤ u
--   - generalization: ŷ_tj = (k − t + 1)[y_j − δ_tj] of (EC.36), after 'WLOG T = 1, v^D_j = y_j' → ŷ_tj = Y_j − (t − 1)v^D_j − (N − t + 1)δ_tj, for general (N, Y); reason: the WLOG is no reduction when constraints do not bind; the formula reduces to (EC.36) at Y = N v^D
--   - encoding: 'suppose α_s = α̂_s and y_s = ŷ_s for s ≤ t − 1' → the same, with two further premises on the earlier periods: σ̂_sj ≠ 0, and a sale at s has y_sj > 0; reason: the first says α̂_s is defined, the second holds on every path of positive probability
-- source:
--   Najafi, Duenyas, Jasin, Uichanco, Multi-product Dynamic Pricing with Limited Inventories under a Cascade Click Model, SSRN abstract_id=3362921, Lemma EC.2, p.ec10; (EC.36), p.ec10

import Mathlib
import Definitions.Def_CascadeCC_Analysis

namespace CascadeCC

variable {J : ℕ}

/-- Lemma EC.2, p.ec10 (SSRN abstract_id=3362921), one inductive step, with the inventory in its general form:
if α_s = α̂_s and y_s = ŷ_s for all s ≤ t − 1, where ŷ_sj = Y_j − (s − 1) v^D_j − (N − s + 1) δ^v_sj, and
‖δ^v_t‖_∞ < φ̂ = φ/2, then α_t = α̂_t and y_t = ŷ_t; moreover α̂_t lies in (0, u) and y_t > 0.

**Formalization Note** Here `h` is the history before period t, so t − 1 = `h.length`, t ≤ N, and its
prefixes `h.take s` are the histories before the earlier periods. The formula for ŷ is the general form of
(EC.36), to which it reduces when Y = N v^D; the printed "WLOG v^D_j = y_j" is not a reduction. Two premises
spell out what the page leaves implicit about the earlier periods: α̂_s is defined (`hdef`), and a sale in
the history has stock to sell (`hsale`), which holds on every path of positive probability. -/
theorem lemma_EC2 (M : Instance J) (T : ℕ) (hT : 0 < T) (y : Fin J → ℝ) (hy : ∀ j, 0 ≤ y j)
    (a : Fin J → ℝ) (ha : IsStationaryOptimal M T y a) (hlam : 0 < M.lam)
    (hau : ∀ j, a j ∈ Set.Ioo 0 M.u) (φ : ℝ) (hφ : IsAdmissible M a φ)
    (k : ℝ) (hk : 1 ≤ k) (N : ℕ) (Y : Fin J → ℕ) (hN : (N : ℝ) = k * T)
    (hY : ∀ j, (Y j : ℝ) = k * y j) (h : List (Option (Fin J))) (hlen : h.length < N)
    (hprev : ∀ s < h.length,
      ccPolicy M N Y a (h.take s) = hatRate M a (ccState M N Y a (h.take s)).corr ∧
        ∀ j, ((ccState M N Y a (h.take s)).inv j : ℝ) =
          (Y j : ℝ) - (s : ℝ) * purchase M a j -
            ((N : ℝ) - s) * (ccState M N Y a (h.take s)).corr j)
    (hdef : ∀ s < h.length, ∀ j : Fin J,
      hatArrival M (hatPurchase M a (ccState M N Y a (h.take s)).corr) j ≠ 0)
    (hsale : ∀ s < h.length, ∀ j : Fin J, h[s]? = some (some j) →
      0 < (ccState M N Y a (h.take s)).inv j)
    (hδ : ‖(ccState M N Y a h).corr‖ < φ / 2) :
    (∀ j, hatRate M a (ccState M N Y a h).corr j ∈ Set.Ioo 0 M.u) ∧
      ccPolicy M N Y a h = hatRate M a (ccState M N Y a h).corr ∧
      (∀ j, 0 < (ccState M N Y a h).inv j) ∧
      ∀ j, ((ccState M N Y a h).inv j : ℝ) =
        (Y j : ℝ) - (h.length : ℝ) * purchase M a j -
          ((N : ℝ) - h.length) * (ccState M N Y a h).corr j := by sorry

end CascadeCC
