-- Prove2me | Theorems.Thm_DQIShattered_theorem_2_4
-- name    : DQIShattered.theorem_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:30:26.528566+00:00
-- url     : https://prove2.me/theorems/15588daf-3e35-4172-a5f9-df85a346c2b3
-- title:
--   Theorem 2.4 — a $(B,\gamma,\delta)$ decoder gives DQI within TV $\varepsilon$ w.p. $\ge1-\sqrt\delta/\varepsilon$ over $J$
-- statement:
--   Let $B\in\mathbb F_2^{M\times N}$, let $J_1,\dots,J_M$ be i.i.d. uniform on $\{+1,-1\}$, and let $H_{B,J}$ be the Hamiltonian (2.5). Fix $\delta\in[0,1]$ and $\beta\ge0$, and let $\gamma=\frac12-\frac12\operatorname{sech}\beta$, that is, $\beta=\operatorname{sech}^{-1}(1-2\gamma)$ (2.6).
--
--   Let $U$ be any unitary decoder that solves the $(B,\gamma,\delta)$-quantum decoding problem, and fix any configuration $z_0$. Then for every $\varepsilon\ge\sqrt\delta$ with $\varepsilon>0$, the DQI output law $\nu^{\mathrm{DQI}}_{B,J,\beta}=K_B\,\mathcal D_{\mathrm{actual}}(B,J,\beta)$ satisfies
--
--   $$\mathbb P_J\Big[d_{\mathrm{TV}}\big(\nu^{\mathrm{DQI}}_{B,J,\beta},\,\mu_{\beta,H_{B,J}}\big)\le\varepsilon\Big]\ \ge\ 1-\frac{\sqrt\delta}{\varepsilon}.$$
--
--   This is the reduction of Gibbs sampling to quantum decoding. Theorem 2.7 applies it with the USD decoder on random $B$.
--
--   Differences from the source:
--   - reading: given a subroutine which efficiently solves the (B, γ, δ)-quantum decoding problem, DQI can efficiently solve the Gibbs sampling problem → for every unitary decoder solving the problem, the exact DQI output law ν^{DQI} satisfies the bound; reason: for one fixed B "efficiently" has no formal content; the efficiency statement is the goal theorem_2_7
--   - reading: γ ∈ [0, 1/2] and β = sech⁻¹(1 − 2γ) → β ≥ 0 and γ = 1/2 − 1/(2 cosh β), i.e. γ ∈ [0, 1/2); reason: γ = 1/2 gives β = sech⁻¹(0) = ∞, where the Gibbs measure (2.1) is not defined
--   - encoding: ε ≥ √δ → ε ≥ √δ and ε > 0; reason: excludes only δ = ε = 0, where √δ/ε is undefined
--   - reading: DQI with the decoder → ν^{DQI} built with compute–copy–uncompute (as in theorem_3_1); reason: see theorem_3_1; for a perfect decoder it is the procedure (3.11)–(3.16)
--   - encoding: probability over the J_i's → the fraction of the 2^M sign vectors v, J = (−1)^v; reason: bijection; same instances
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), Theorem 2.4, p.5; proof pp.12–13

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_DQIShattered_DQI

namespace DQIShattered

open Finset

/-- Zhou, Shutty, Sellke, Jordan, *Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry*,
arXiv:2609.40345, held version sha256 0c7f6fdf…, Theorem 2.4, p.5 (proof pp.12–13).

Let `B ∈ 𝔽₂^{M×N}`, `J₁, …, J_M` i.i.d. uniform on `{+1, −1}`, `H_{B,J}` as in (2.5). Fix `δ ∈ [0, 1]` and
`β ≥ 0`, with `γ = 1/2 − (1/2) sech β`, i.e. `β = sech⁻¹(1 − 2γ)` (2.6). For every unitary `U` solving the
`(B, γ, δ)`-quantum decoding problem, every fixed `z₀` and every `ε ≥ √δ` (`ε > 0`), the DQI output law
`ν^{DQI}_{B,J,β} = K_B 𝒟_actual(B, J, β)` satisfies
`P_J[d_TV(ν^{DQI}_{B,J,β}, µ_{β,H_{B,J}}) ≤ ε] ≥ 1 − √δ/ε`.

**Formalization Note** "Efficiently" has no content for one fixed `B`; it is in Theorem 2.7 (`theorem_2_7`). The
probability over `J` is the fraction of the `2^M` sign vectors `v`, `J = (−1)^v`. -/
theorem theorem_2_4 {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2)) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (β : ℝ) (hβ : 0 ≤ β) {W : Type} [Fintype W] [DecidableEq W]
    (U : Matrix (Reg M × Reg M × W) (Reg M × Reg M × W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Reg M × Reg M × W) ℂ) (w₀ : W)
    (hsolve : SolvesDecoding B (gammaOf β) δ U w₀) (x₀ : Fin N → ZMod 2) (ε : ℝ) (hε : 0 < ε)
    (hεδ : Real.sqrt δ ≤ ε) :
    1 - Real.sqrt δ / ε ≤
      ((univ.filter fun v : Fin M → ZMod 2 =>
          IsingLTL.BeliefProp.tvDist (nuDQI B v β U w₀ x₀) (gibbs B v β) ≤ ε).card : ℝ) / 2 ^ M := by sorry

end DQIShattered
