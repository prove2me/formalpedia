-- Prove2me | Theorems.Thm_BilateralRegret_term_I
-- name    : BilateralRegret.term_I
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:14:11.053987+00:00
-- url     : https://prove2.me/theorems/d976f335-af8a-41ba-abe0-5881cd591c4c
-- title:
--   Proof of Theorem 3, term (I) — $(\mathrm I)\le4M|p^\star-q_{k^\star}|(T-T_0)\le\frac{4M}{K+1}(T-T_0)$
-- statement:
--   Throughout, $(S_t,B_t)_{t\le T}$ are i.i.d. seller/buyer valuation pairs with law $\mu_S\otimes\mu_B$, where $\mu_S,\mu_B$ are probability measures on $[0,1]$ (stochastic i.i.d. setting with independent valuations), and $U_1,\dots,U_T$ are i.i.d. uniform on $[0,1]$ and independent of the valuations (the player's randomization). Scouting Bandits (SB) is run with exploration time $T_0\ge1$, grid size $K\ge1$ and a measurable $K$-armed bandit strategy $\alpha$, on a horizon $T\ge T_0$; $q_k=k/(K+1)$ are the grid prices, $\widehat F_k=\frac1{T_0}\sum_{s\le T_0}\mathbb I\{q_k\le U_s\le B_s\}$ and $\widehat G_k=\frac1{T_0}\sum_{s\le T_0}\mathbb I\{S_s\le U_s\le q_k\}$ are the scouting estimates, $Z_{H,t}(k)=\mathbb I\{S_t\le q_k\}\widehat F_k+\mathbb I\{q_k\le B_t\}\widehat G_k$ is the surrogate reward, $I_{H,t}$ is the arm SB plays in round $t>T_0$, $P_t$ is the price SB posts, and $\mathrm{GFT}_t(p)=\mathrm{GFT}(p,S_t,B_t)$. The seller's and the buyer's valuation laws have densities bounded by $M$.
--
--   Let $p^\star\in[0,1]$ and let $k^\star$ be the index of a grid point closest to $p^\star$. Then
--
--   $$
--   (\mathrm I)=\sum_{t=T_0+1}^T\Big(\mathbb E[\mathrm{GFT}_t(p^\star)]-\mathbb E[\mathrm{GFT}_t(q_{k^\star})]\Big)\le4M|p^\star-q_{k^\star}|(T-T_0)\le\frac{4M}{K+1}(T-T_0).
--   $$
--
--   This is the discretization error of the grid.
--
--   Differences from the source:
--   - encoding: rounds t = 1, …, T → indices t − 1 : Fin T; the bandit-phase rounds t = T₀+1, …, T are banditRounds T₀ T; reason: Lean indexing; same instances
--   - encoding: the seller/buyer pairs (S_t, B_t) ∈ [0,1]² are i.i.d. with S_t independent of B_t (iid + iv) → the sample space (Fin T → ℝ × ℝ) × (Fin T → ℝ) with the product law (μ_S ⊗ μ_B)^{⊗T} ⊗ Unif[0,1]^{⊗T}, μ_S, μ_B probability measures on ℝ with μ((Icc 0 1)ᶜ) = 0; reason: Definition 2 and App. C.2.3 (pp.23–24) truncated to T rounds; same instances
--   - encoding: SB draws U_t uniformly for t ≤ T₀, and α uses its own internal randomization V_t → one i.i.d. Uniform[0,1] sequence U_t, independent of the valuations: SB posts U_t for t ≤ T₀ and passes U_{T₀+1}, U_{T₀+2}, … to α as its uniforms; reason: the player's randomization of Definition 2 (p.23); the paper's U_t and V_t are such independent uniforms (paper.md R2)
--   - reading: exploration time T₀ (no range stated) → 1 ≤ T₀, together with 1 ≤ K and T₀ ≤ T; reason: Algorithm 3 divides by T₀ and the bound contains √(2π/T₀); T₀ = 0 is undefined (paper.md R4)
--   - encoding: grid q_k = k/(K+1), k ∈ [K] → grid K k = (k+1)/(K+1) for k : Fin K; reason: zero-based arm indices; same grid
--   - generalization: the valuations have densities bounded by M; (bd), p.6 and p.24: the joint density of (S₁, B₁) is bounded by M → each of μ_S, μ_B satisfies μ(A) ≤ M · Leb(A) for every Borel A; reason: a joint density f ≤ M on [0,1]² gives marginal densities ∫ f ≤ M, so every instance of the source is covered; the printed proof only uses the marginals (paper.md R1)
--   - generalization: p★ ∈ argmax_{p∈[0,1]} E[GFT(p, S₁, B₁)] → any p★ ∈ [0,1]; reason: the bound only uses the Lipschitz property; the argmax is an instance
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Fusco, Leonardi, Bilateral Trade: A Regret Minimization Perspective, arXiv:2109.12974v1, proof of Theorem 3, term (I), p.12

import Mathlib
import Definitions.Def_BilateralRegret_sbPrice

namespace BilateralRegret

open MeasureTheory

/-- **Proof of Theorem 3, term (I).**
Cesa-Bianchi, Cesari, Colomboni, Fusco, Leonardi, *Bilateral Trade: A Regret Minimization
Perspective*, arXiv:2109.12974v1, §5.1, p.12.

If the seller's and buyer's valuation laws have densities bounded by `M`, then for every
`p★ ∈ [0,1]` and every index `k★` of a grid point `q_{k★}` closest to `p★`,
`(I) = Σ_{t=T₀+1}^T (𝔼[GFT_t(p★)] − 𝔼[GFT_t(q_{k★})]) ≤ 4M |p★ − q_{k★}| (T − T₀) ≤ 4M/(K+1) (T − T₀)`.

**Formalization Note.** Setting of Theorem 3: the round-`t` valuation pairs are i.i.d. with law
`μ_S ⊗ μ_B` (stochastic (iid) with independent valuations (iv)), `μ_S`, `μ_B` are probability
measures on `ℝ` concentrated on `[0,1]`, and the player's uniform draws `U_t` are i.i.d. uniform on
`[0,1]` and independent of the valuations (`scenario`). Rounds `t = 1, …, T` are `Fin T`
(round `t` = index `t − 1`); the bandit-phase rounds `t = T₀+1, …, T` are `banditRounds T₀ T`.
`T₀ ≥ 1` (Algorithm 3 divides by `T₀`), `K ≥ 1`, `T ≥ T₀`.
The density bound is `μ(A) ≤ M · Leb(A)` for each of `μ_S`, `μ_B` separately. -/
theorem term_I (μS μB : Measure ℝ) [IsProbabilityMeasure μS] [IsProbabilityMeasure μB]
    (hS : μS (Set.Icc (0 : ℝ) 1)ᶜ = 0) (hB : μB (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (T₀ K T : ℕ) (hT₀ : 1 ≤ T₀) (hK : 1 ≤ K) (hT : T₀ ≤ T)
    (M : ℝ) (hMS : DensityBoundedBy M μS) (hMB : DensityBoundedBy M μB)
    (pstar : ℝ) (hpstar : pstar ∈ Set.Icc (0 : ℝ) 1) (kstar : Fin K)
    (hkstar : ∀ k : Fin K, |pstar - grid K kstar| ≤ |pstar - grid K k|) :
    ∑ t ∈ banditRounds T₀ T,
        ((∫ ω, GFT pstar (sellerVal ω t) (buyerVal ω t) ∂(scenario μS μB T))
          - ∫ ω, GFT (grid K kstar) (sellerVal ω t) (buyerVal ω t) ∂(scenario μS μB T))
        ≤ 4 * M * |pstar - grid K kstar| * ((T : ℝ) - T₀) ∧
      4 * M * |pstar - grid K kstar| * ((T : ℝ) - T₀) ≤ 4 * M / ((K : ℝ) + 1) * ((T : ℝ) - T₀) := by sorry

end BilateralRegret
