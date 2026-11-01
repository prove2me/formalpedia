-- Prove2me | Theorems.Thm_BilateralRegret_eq_9_first
-- name    : BilateralRegret.eq_9_first
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:14:06.44868+00:00
-- url     : https://prove2.me/theorems/686f7c74-6219-419e-96e4-224b9d97969d
-- title:
--   Proof of Theorem 3, (9) first inequality — $R_T(\mathrm{SB})\le T_0+\sum_{t>T_0}\mathbb E[\mathrm{GFT}_t(p^\star)-\mathrm{GFT}_t(P_t)]$
-- statement:
--   Throughout, $(S_t,B_t)_{t\le T}$ are i.i.d. seller/buyer valuation pairs with law $\mu_S\otimes\mu_B$, where $\mu_S,\mu_B$ are probability measures on $[0,1]$ (stochastic i.i.d. setting with independent valuations), and $U_1,\dots,U_T$ are i.i.d. uniform on $[0,1]$ and independent of the valuations (the player's randomization). Scouting Bandits (SB) is run with exploration time $T_0\ge1$, grid size $K\ge1$ and a measurable $K$-armed bandit strategy $\alpha$, on a horizon $T\ge T_0$; $q_k=k/(K+1)$ are the grid prices, $\widehat F_k=\frac1{T_0}\sum_{s\le T_0}\mathbb I\{q_k\le U_s\le B_s\}$ and $\widehat G_k=\frac1{T_0}\sum_{s\le T_0}\mathbb I\{S_s\le U_s\le q_k\}$ are the scouting estimates, $Z_{H,t}(k)=\mathbb I\{S_t\le q_k\}\widehat F_k+\mathbb I\{q_k\le B_t\}\widehat G_k$ is the surrogate reward, $I_{H,t}$ is the arm SB plays in round $t>T_0$, $P_t$ is the price SB posts, and $\mathrm{GFT}_t(p)=\mathrm{GFT}(p,S_t,B_t)$.
--
--   Let $p^\star\in[0,1]$ maximize $p\mapsto\mathbb E[\mathrm{GFT}(p,S_1,B_1)]$ over $[0,1]$. Then
--
--   $$
--   R_T(\mathrm{SB})\le T_0+\sum_{t=T_0+1}^T\mathbb E\big[\mathrm{GFT}_t(p^\star)-\mathrm{GFT}_t(P_t)\big].
--   $$
--
--   Each scouting round costs at most $1$ in regret; the rest of the analysis bounds the bandit-phase sum, which the paper splits into the terms (I)–(IV).
--
--   Differences from the source:
--   - encoding: rounds t = 1, …, T → indices t − 1 : Fin T; the bandit-phase rounds t = T₀+1, …, T are banditRounds T₀ T; reason: Lean indexing; same instances
--   - encoding: the seller/buyer pairs (S_t, B_t) ∈ [0,1]² are i.i.d. with S_t independent of B_t (iid + iv) → the sample space (Fin T → ℝ × ℝ) × (Fin T → ℝ) with the product law (μ_S ⊗ μ_B)^{⊗T} ⊗ Unif[0,1]^{⊗T}, μ_S, μ_B probability measures on ℝ with μ((Icc 0 1)ᶜ) = 0; reason: Definition 2 and App. C.2.3 (pp.23–24) truncated to T rounds; same instances
--   - encoding: SB draws U_t uniformly for t ≤ T₀, and α uses its own internal randomization V_t → one i.i.d. Uniform[0,1] sequence U_t, independent of the valuations: SB posts U_t for t ≤ T₀ and passes U_{T₀+1}, U_{T₀+2}, … to α as its uniforms; reason: the player's randomization of Definition 2 (p.23); the paper's U_t and V_t are such independent uniforms (paper.md R2)
--   - reading: exploration time T₀ (no range stated) → 1 ≤ T₀, together with 1 ≤ K and T₀ ≤ T; reason: Algorithm 3 divides by T₀ and the bound contains √(2π/T₀); T₀ = 0 is undefined (paper.md R4)
--   - encoding: grid q_k = k/(K+1), k ∈ [K] → grid K k = (k+1)/(K+1) for k : Fin K; reason: zero-based arm indices; same grid
--   - encoding: 𝔼[GFT(p, S₁, B₁)] → ∫ GFT p x.1 x.2 ∂(μ_S ⊗ μ_B); reason: (S₁, B₁) has law μ_S ⊗ μ_B; same value
--   - encoding: Σ_{t=T₀+1}^T E[GFT_t(p★) − GFT_t(P_t)] → the sum over banditRounds T₀ T of the integral of the difference; reason: same expression
--   - encoding: R_T = max_{p ∈ [0,1]} 𝔼[Σ GFT(p, S_t, B_t) − Σ GFT(P_t, S_t, B_t)] → the real ⨆ over the subtype [0,1] (regret); reason: the family is bounded by T in absolute value, so ⨆ is the true supremum; a maximizer is not presupposed (paper.md R6)
--   - encoding: a K-armed bandit algorithm α, possibly randomized → a measurable strategy of Definition 3 (BanditStrategy K) that maps its real-valued uniforms and past rewards to an arm; reason: Definition 3 with feedback space ℝ; a strategy on [0,1]^t × [0,1]^(t−1) extends measurably, and a run reads values outside that domain only on a null set
--   - generalization: the setting of Theorem 3 assumes valuation laws with densities bounded by M → no density hypothesis on μ_S, μ_B; reason: this step does not use the density bound; the setting of Theorem 3 is an instance
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Fusco, Leonardi, Bilateral Trade: A Regret Minimization Perspective, arXiv:2109.12974v1, proof of Theorem 3, (9), first inequality, p.12

import Mathlib
import Definitions.Def_BilateralRegret_sbPrice

namespace BilateralRegret

open MeasureTheory

/-- **Proof of Theorem 3, (9), first inequality.**
Cesa-Bianchi, Cesari, Colomboni, Fusco, Leonardi, *Bilateral Trade: A Regret Minimization
Perspective*, arXiv:2109.12974v1, §5.1, p.12.

Let `p★ ∈ argmax_{p ∈ [0,1]} 𝔼[GFT(p, S_1, B_1)]` and let `P_t` be the price posted by Scouting
Bandits (SB) in round `t`. Then
`R_T(SB) ≤ T₀ + Σ_{t=T₀+1}^T 𝔼[GFT_t(p★) − GFT_t(P_t)]`, where `GFT_t(p) = GFT(p, S_t, B_t)`.

**Formalization Note.** Setting of Theorem 3: the round-`t` valuation pairs are i.i.d. with law
`μ_S ⊗ μ_B` (stochastic (iid) with independent valuations (iv)), `μ_S`, `μ_B` are probability
measures on `ℝ` concentrated on `[0,1]`, and the player's uniform draws `U_t` are i.i.d. uniform on
`[0,1]` and independent of the valuations (`scenario`). Rounds `t = 1, …, T` are `Fin T`
(round `t` = index `t − 1`); the bandit-phase rounds `t = T₀+1, …, T` are `banditRounds T₀ T`.
`T₀ ≥ 1` (Algorithm 3 divides by `T₀`), `K ≥ 1`, `T ≥ T₀`.
`𝔼[GFT(p, S_1, B_1)]` is the integral against the law `μ_S ⊗ μ_B` of `(S_1, B_1)`. -/
theorem eq_9_first (μS μB : Measure ℝ) [IsProbabilityMeasure μS] [IsProbabilityMeasure μB]
    (hS : μS (Set.Icc (0 : ℝ) 1)ᶜ = 0) (hB : μB (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (T₀ K T : ℕ) (hT₀ : 1 ≤ T₀) (hK : 1 ≤ K) (hT : T₀ ≤ T)
    (α : BanditStrategy K) (pstar : ℝ) (hpstar : pstar ∈ Set.Icc (0 : ℝ) 1)
    (hmax : ∀ p ∈ Set.Icc (0 : ℝ) 1,
      ∫ x, GFT p x.1 x.2 ∂(μS.prod μB) ≤ ∫ x, GFT pstar x.1 x.2 ∂(μS.prod μB)) :
    regret T μS μB (sbPrice T₀ K α T) ≤ (T₀ : ℝ) + ∑ t ∈ banditRounds T₀ T,
      ∫ ω, (GFT pstar (sellerVal ω t) (buyerVal ω t)
        - GFT (sbPrice T₀ K α T ω t) (sellerVal ω t) (buyerVal ω t)) ∂(scenario μS μB T) := by sorry

end BilateralRegret
