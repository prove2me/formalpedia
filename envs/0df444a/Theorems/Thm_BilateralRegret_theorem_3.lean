-- Prove2me | Theorems.Thm_BilateralRegret_theorem_3
-- name    : BilateralRegret.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:14:30.795645+00:00
-- url     : https://prove2.me/theorems/497213d7-4e52-4f4a-832d-56b1cf17aebc
-- title:
--   Theorem 3 — Scouting Bandits: $R_T(\mathrm{SB})\le T_0+\big(\frac{4M}{K+1}+\sqrt{2\pi/T_0}\big)(T-T_0)+\mathcal R_{T-T_0}(\alpha)$, and $O(MT^{2/3})$ with tuned parameters
-- statement:
--   Consider bilateral trade with realistic feedback (after posting $P_t$ the learner only observes $\mathbb I\{S_t\le P_t\}$ and $\mathbb I\{P_t\le B_t\}$) in the stochastic i.i.d. setting: the seller/buyer pairs $(S_t,B_t)$ are i.i.d. with law $\mu_S\otimes\mu_B$ (independent valuations), where $\mu_S,\mu_B$ are laws on $[0,1]$ with densities bounded by $M$. Let SB be Scouting Bandits (Algorithm 3) run with exploration time $T_0\ge1$, grid size $K\ge1$ and a measurable $K$-armed bandit strategy $\alpha$.
--
--   1. For every horizon $T\ge T_0$,
--
--   $$
--   R_T(\mathrm{SB})\le T_0+\left(\frac{4M}{K+1}+\sqrt{\frac{2\pi}{T_0}}\right)(T-T_0)+\mathcal R_{T-T_0}(\alpha),
--   $$
--
--   where $\mathcal R_\tau(\alpha)$ is any distribution-free upper bound on the regret of $\alpha$ after $\tau$ rounds in the stochastic i.i.d. bandit setting with $[0,1]$-valued rewards (every law of the reward vector on $[0,1]^K$).
--
--   2. Let $C\ge0$. There is a constant $c$, depending only on $C$, such that the following holds. If for each $K\ge1$ and each horizon $\tau$ the bandit strategy $\alpha^{K,\tau}$ over $K$ arms, which may be tuned to $\tau$, has $\mathcal R_\tau(\alpha^{K,\tau})\le C\sqrt{K\tau}$ (for instance MOSS; a single $\alpha^K$ for each $K$ is the case that does not depend on $\tau$), then running SB with $T_0=\lceil T^{2/3}\rceil$, $K=\lceil T^{1/3}\rceil$ and $\alpha^{K,T-T_0}$ gives
--
--   $$
--   R_T(\mathrm{SB})\le c\,M\,T^{2/3}\qquad\text{for every }T\ge1,
--   $$
--
--   for every $M$ and every pair of laws as above.
--
--   This is the paper's positive result for posted-price (realistic-feedback) bilateral trade; the matching $\Omega(T^{2/3})$ lower bound is Theorem 4.
--
--   Differences from the source:
--   - encoding: rounds t = 1, …, T → indices t − 1 : Fin T; the bandit-phase rounds t = T₀+1, …, T are banditRounds T₀ T; reason: Lean indexing; same instances
--   - encoding: the seller/buyer pairs (S_t, B_t) ∈ [0,1]² are i.i.d. with S_t independent of B_t (iid + iv) → the sample space (Fin T → ℝ × ℝ) × (Fin T → ℝ) with the product law (μ_S ⊗ μ_B)^{⊗T} ⊗ Unif[0,1]^{⊗T}, μ_S, μ_B probability measures on ℝ with μ((Icc 0 1)ᶜ) = 0; reason: Definition 2 and App. C.2.3 (pp.23–24) truncated to T rounds; same instances
--   - encoding: SB draws U_t uniformly for t ≤ T₀, and α uses its own internal randomization V_t → one i.i.d. Uniform[0,1] sequence U_t, independent of the valuations: SB posts U_t for t ≤ T₀ and passes U_{T₀+1}, U_{T₀+2}, … to α as its uniforms; reason: the player's randomization of Definition 2 (p.23); the paper's U_t and V_t are such independent uniforms (paper.md R2)
--   - reading: exploration time T₀ (no range stated) → 1 ≤ T₀, together with 1 ≤ K and T₀ ≤ T; reason: Algorithm 3 divides by T₀ and the bound contains √(2π/T₀); T₀ = 0 is undefined (paper.md R4)
--   - encoding: grid q_k = k/(K+1), k ∈ [K] → grid K k = (k+1)/(K+1) for k : Fin K; reason: zero-based arm indices; same grid
--   - generalization: the valuations have densities bounded by M; (bd), p.6 and p.24: the joint density of (S₁, B₁) is bounded by M → each of μ_S, μ_B satisfies μ(A) ≤ M · Leb(A) for every Borel A; reason: a joint density f ≤ M on [0,1]² gives marginal densities ∫ f ≤ M, so every instance of the source is covered; the printed proof only uses the marginals (paper.md R1)
--   - reading: R_τ(α) is a distribution-free upper bound on the regret after τ rounds of α in the stochastic i.i.d. setting with [0,1]-valued rewards → any real R with banditRegret α ν τ ≤ R for every probability law ν on reward vectors ℝ^K with ν([0,1]^K) = 1 (arms may be correlated); α is a measurable strategy of Definition 3 that maps its real-valued uniforms and past rewards to an arm (a strategy on [0,1]^t × [0,1]^(t−1) extends measurably, and a run reads values outside that domain only on a null set); reason: the paper's own framework, Definitions 1–4 and App. C.2.3 (paper.md R3); taking R as a universal upper bound is equivalent to taking the supremum
--   - encoding: R_T = max_{p ∈ [0,1]} 𝔼[Σ GFT(p, S_t, B_t) − Σ GFT(P_t, S_t, B_t)] → the real ⨆ over the subtype [0,1] (regret); reason: the family is bounded by T in absolute value, so ⨆ is the true supremum; a maximizer is not presupposed (paper.md R6)
--   - reading: if R_τ(α^K) = O(√(Kτ)) … R_T(SB) = O(M T^{2/3}) → ∀ C ≥ 0, ∃ c, for every family with banditRegret (α K τ hK) ν τ ≤ C√(Kτ) for all K ≥ 1, τ and admissible ν, and every M, μ_S, μ_B as in (a): R_T(SB) ≤ c·M·T^{2/3} for all T ≥ 1; reason: c depends on the O-constant C only; the bound holds for every T ≥ 1, not only eventually (paper.md R5)
--   - encoding: T₀ := ⌈T^{2/3}⌉ and K := ⌈T^{1/3}⌉, a bandit algorithm α^K for each K → ⌈(T:ℝ)^(2/3)⌉₊, ⌈(T:ℝ)^(1/3)⌉₊, and a family indexed by hK : 1 ≤ K; reason: natural-number ceilings; there is no strategy over 0 arms, and K = ⌈T^{1/3}⌉ ≥ 1 for T ≥ 1
--   - generalization: a bandit algorithm α^K for each K, with R_τ(α^K) = O(√(Kτ)), e.g. MOSS → a family α K τ hK that may also depend on the horizon τ, with the bound required of α K τ hK at horizon τ only, and SB runs α K (T − T₀) hK; reason: MOSS takes the horizon as an input (Audibert and Bubeck, 2009), so the paper's example is covered only this way; a single α^K for each K is the family constant in τ
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Fusco, Leonardi, Bilateral Trade: A Regret Minimization Perspective, arXiv:2109.12974v1, Theorem 3, p.12 (§5.1; Algorithm 3, p.11; proof pp.12–13)

import Mathlib
import Definitions.Def_BilateralRegret_sbPrice

namespace BilateralRegret

open MeasureTheory

/-- **Theorem 3 (Scouting Bandits under realistic feedback).**
Cesa-Bianchi, Cesari, Colomboni, Fusco, Leonardi, *Bilateral Trade: A Regret Minimization
Perspective*, arXiv:2109.12974v1, §5.1, p.12.

In the realistic-feedback stochastic (iid) setting where the valuations of the seller and the
buyer are independent (iv) and have densities bounded by `M`:

(a) the regret of Scouting Bandits (SB) run with parameters `T₀`, `K`, `α` satisfies, for every
horizon `T ≥ T₀`, `R_T(SB) ≤ T₀ + (4M/(K+1) + √(2π/T₀)) (T − T₀) + R_{T−T₀}(α)`, where `R_τ(α)` is any
distribution-free upper bound on the regret of `α` after `τ` rounds in the stochastic i.i.d.
setting with `[0,1]`-valued rewards;

(b) if for each `K` the bandit algorithm `α^K` over `K` arms, which may be tuned to the horizon `τ`,
has `R_τ(α^K) ≤ C √(Kτ)` (for all `K ≥ 1`, all `τ`, all such reward laws), then with `T₀ = ⌈T^{2/3}⌉`
and `K = ⌈T^{1/3}⌉`, `R_T(SB) ≤ c M T^{2/3}` for every `T ≥ 1`, with a constant `c` that depends only
on `C`.

**Formalization Note.** Rounds are `Fin T` (round `t` = index `t − 1`); the grid is
`q_k = (k+1)/(K+1)` for `k : Fin K`; valuation laws are probability measures on `ℝ` concentrated on
`[0,1]`, and the density bound is `μ(A) ≤ M · Leb(A)` for each of `μ_S`, `μ_B` (not a joint density
bound); the player's randomization is one i.i.d. uniform sequence, used by SB as its scouting
prices and as `α`'s internal randomization; a bandit scenario is an i.i.d. law `ν` on reward vectors
concentrated on `[0,1]^K`, with correlated arms allowed; `α` is measurable; `T₀ ≥ 1`; the regret is
the real supremum over `p ∈ [0,1]` (`regret`). In (b) the family `α K τ hK` is indexed by `K ≥ 1`
(there is no strategy over `0` arms) and by the horizon `τ` it is tuned to (MOSS, the paper's example,
takes the horizon as an input; one `α^K` for each `K` is the family constant in `τ`), SB runs
`α K (T − T₀) hK`, `T₀`, `K` are the ceilings `⌈T^{2/3}⌉`, `⌈T^{1/3}⌉`, and `∃ c` comes right after
`C`, so `c` does not depend on the family, `M`, the laws or `T`. -/
theorem theorem_3 :
    (∀ (M : ℝ) (μS μB : Measure ℝ) [IsProbabilityMeasure μS] [IsProbabilityMeasure μB],
      μS (Set.Icc (0 : ℝ) 1)ᶜ = 0 → μB (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
      DensityBoundedBy M μS → DensityBoundedBy M μB →
      ∀ (T₀ K T : ℕ), 1 ≤ T₀ → 1 ≤ K → T₀ ≤ T →
      ∀ (α : BanditStrategy K) (R : ℝ),
        (∀ ν : Measure (Fin K → ℝ), IsRewardLaw ν → banditRegret α ν (T - T₀) ≤ R) →
        regret T μS μB (sbPrice T₀ K α T)
          ≤ (T₀ : ℝ) + (4 * M / ((K : ℝ) + 1) + Real.sqrt (2 * Real.pi / T₀)) * ((T : ℝ) - T₀)
            + R) ∧
    (∀ C : ℝ, 0 ≤ C → ∃ c : ℝ, ∀ α : (K τ : ℕ) → 1 ≤ K → BanditStrategy K,
      (∀ (K : ℕ) (hK : 1 ≤ K) (τ : ℕ) (ν : Measure (Fin K → ℝ)), IsRewardLaw ν →
        banditRegret (α K τ hK) ν τ ≤ C * Real.sqrt ((K : ℝ) * τ)) →
      ∀ (M : ℝ) (μS μB : Measure ℝ) [IsProbabilityMeasure μS] [IsProbabilityMeasure μB],
        μS (Set.Icc (0 : ℝ) 1)ᶜ = 0 → μB (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
        DensityBoundedBy M μS → DensityBoundedBy M μB →
        ∀ T : ℕ, 1 ≤ T → ∀ hK : 1 ≤ ⌈(T : ℝ) ^ ((1 : ℝ) / 3)⌉₊,
          regret T μS μB
              (sbPrice ⌈(T : ℝ) ^ ((2 : ℝ) / 3)⌉₊ ⌈(T : ℝ) ^ ((1 : ℝ) / 3)⌉₊
                (α ⌈(T : ℝ) ^ ((1 : ℝ) / 3)⌉₊ (T - ⌈(T : ℝ) ^ ((2 : ℝ) / 3)⌉₊) hK) T)
            ≤ c * M * (T : ℝ) ^ ((2 : ℝ) / 3)) := by sorry

end BilateralRegret
