-- Prove2me | Theorems.Thm_AnytimeAdaVR_eq_65_66
-- name    : AnytimeAdaVR.eq_65_66
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:31:24.436199+00:00
-- url     : https://prove2.me/theorems/bcf26589-5892-4abc-b471-8cb259ce2518
-- title:
--   App. G.2 (65)–(66) — $S\le2\cdot10^8P^{5/2}$, $M\le2\cdot10^8P_{\mathrm{av}}^{5/2}$, $D_0\le4P_0$
-- statement:
--   Let $C_\gamma(\Lambda)$ and $D_0$ be the coefficients (63) and (50).
--
--   1. (66) If $W\ge1$, $0\le\Delta_f\le W$, $0\le L\le\sqrt W$, $\sigma,\Lambda\ge0$ and $\sigma^2+\Lambda^2\le W$, then for $\gamma\in\{1/4,1/3\}$,
--   $$
--   C_\gamma(\Lambda)\le 2\cdot10^8\,W^{5/2}.
--   $$
--   2. (65) With $P=1+\Delta_f+L^2+\sigma^2$, $P_{\mathrm{av}}=P+\bar L^2$ and $P_0=1+\Delta_f+L^2$, for all $\Delta_f,L,\sigma,\bar L\ge0$:
--   $$
--   S=C_{1/4}(L)\le2\cdot10^8P^{5/2},\qquad M=C_{1/3}(\bar L)\le2\cdot10^8P_{\mathrm{av}}^{5/2},\qquad D_0\le4P_0 .
--   $$
--
--   These envelopes turn the explicit path coefficients into the polynomial form of Theorem 2.
--
--   Differences from the source:
--   - generalization: L > 0 (Assumption 1) → L ≥ 0; reason: the bounds are stated for every L ≥ 0, which contains the paper's L > 0
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), App. G.2, eqs. (64)–(66), p.31

import Mathlib
import Definitions.Def_AnytimeAdaVR_coefCgamma
import Definitions.Def_AnytimeAdaVR_coefD0

namespace AnytimeAdaVR

/-- **App. G.2, eqs. (65)–(66): the polynomial envelope of the path coefficients.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), App. G.2,
p.31: "Write P = 1 + ∆f + L² + σ², P_av = P + L̄², P_0 = 1 + ∆f + L². (64) The path coefficients
satisfy S ≤ 2·10⁸ P^{5/2}, M ≤ 2·10⁸ P_av^{5/2}, D_0 ≤ 4P_0. (65)" and its proof: "Let W ≥ 1 satisfy
∆f ≤ W, L ≤ √W, and σ² + Λ² ≤ W. … substitution proves C_γ(Λ) ≤ 2·10⁸ W^{5/2}, γ ∈ {1/4, 1/3}. (66)"

1. (66) For `W ≥ 1`, `0 ≤ ∆f ≤ W`, `0 ≤ L ≤ √W`, `σ, Λ ≥ 0` with `σ² + Λ² ≤ W`, and
   `γ ∈ {1/4, 1/3}`: `C_γ(Λ) ≤ 2·10⁸ W^{5/2}`.
2. (65) For `∆f, L, σ, L̄ ≥ 0`: `S = C_{1/4}(L) ≤ 2·10⁸ P^{5/2}`, `M = C_{1/3}(L̄) ≤ 2·10⁸ P_av^{5/2}`
   and `D_0 ≤ 4P_0`.

**Formalization Note.** Pure real arithmetic on the coefficients (63), (50); powers `W^{5/2}`, `9^γ`
are `Real.rpow`. The paper's constants are nonnegative (`L > 0`, `∆f ≥ 0`, `σ ≥ 0`, `L̄ ≥ 0`);
`L = 0` is also allowed. -/
theorem eq_65_66 :
    (∀ W Δf L σ Λ γ : ℝ, 1 ≤ W → 0 ≤ Δf → Δf ≤ W → 0 ≤ L → L ≤ Real.sqrt W → 0 ≤ σ → 0 ≤ Λ →
      σ ^ 2 + Λ ^ 2 ≤ W → (γ = 1 / 4 ∨ γ = 1 / 3) →
        coefCgamma γ Δf L σ Λ ≤ 2 * 10 ^ 8 * W ^ (5 / 2 : ℝ)) ∧
    (∀ Δf L σ Lbar : ℝ, 0 ≤ Δf → 0 ≤ L → 0 ≤ σ → 0 ≤ Lbar →
      coefCgamma (1 / 4) Δf L σ L ≤ 2 * 10 ^ 8 * (1 + Δf + L ^ 2 + σ ^ 2) ^ (5 / 2 : ℝ) ∧
      coefCgamma (1 / 3) Δf L σ Lbar ≤
        2 * 10 ^ 8 * (1 + Δf + L ^ 2 + σ ^ 2 + Lbar ^ 2) ^ (5 / 2 : ℝ) ∧
      coefD0 Δf L ≤ 4 * (1 + Δf + L ^ 2)) := by sorry

end AnytimeAdaVR
