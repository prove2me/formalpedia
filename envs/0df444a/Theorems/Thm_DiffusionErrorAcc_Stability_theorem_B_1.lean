-- Prove2me | Theorems.Thm_DiffusionErrorAcc_Stability_theorem_B_1
-- name    : DiffusionErrorAcc.Stability.theorem_B_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:59:25.554304+00:00
-- url     : https://prove2.me/theorems/3a187c01-ef29-454c-a935-bde18040a330
-- title:
--   Theorem B.1 — the learned reverse SDE errs on f by at most η_T + 2ε_score√(1 + log C_f) + ε²_score T, C_f = max(C_P(p; f), 1)
-- statement:
--   Fix a dimension $d\ge1$, a horizon $T>0$ and a ground-truth law $p$ on $\mathbb R^d$ with positive $C^1$ density. The forward Ornstein–Uhlenbeck process has marginals $p_t=\mathrm{Law}(e^{-t}Z_0+\sqrt{1-e^{-2t}}\,G)$, $Z_0\sim p$, $G\sim N(0,I_d)$, and scores $\nabla\log p_t$. A learned score $\hat s:\mathbb R^d\times[0,T]\to\mathbb R^d$ satisfies Assumption 2.1,
--   $$\mathbb E_{p_t}\|\hat s_t(x)-\nabla\log p_t(x)\|^2\le\varepsilon_{\mathrm{score}}^2\qquad(0<t<T),$$
--   and both $\nabla\log p_t(x)$ and $\hat s_t(x)$ are Lipschitz in $x$ uniformly in $t$ and continuous in $(x,t)$. The learned reverse SDE (2.2) is $dY_u=(Y_u+2\hat s_{T-u}(Y_u))\,du+\sqrt2\,dB_u$, $Y_0\sim\nu_0$, $0\le u\le T$, with output law $\hat p_T=\mathrm{Law}(Y_T)$ and initialization error $\eta_T=\mathrm{TV}(\nu_0,p_T)$.
--
--   Let $f:\mathbb R^d\to[0,1]$ be a test statistic (uniformly continuous and $C^2$) with $\mathrm{Var}_p(f)>0$, and $C_f=\max(C_P(p;f),1)$ with $C_P(p;f)$ the f-conditioned Poincaré constant. Then
--   $$\big|\mathbb E_{\hat p_T}f-\mathbb E_pf\big|\le\eta_T+2\varepsilon_{\mathrm{score}}\sqrt{1+\log C_f}+\varepsilon_{\mathrm{score}}^2T .$$
--   The bound holds for every initial law, every standard Brownian motion $B$ and every solution $Y$ with $Y_0\sim\nu_0$ independent of $B$: the error on $f$ is controlled by the score error through $\sqrt{\log C_P(p;f)}$, with no polynomial dependence on $T$ in the leading term.
--
--   **Formalization Note.** The statement quantifies over every probability space `Ω : Type`, every `B` with `EthierKurtz.IsStandardBrownian P B` and every pathwise solution `Y` of (2.2); $\eta_T$ is `tvDist ν₀ (ouMarginal ρ T)`.
--
--   Differences from the source:
--   - generalization: ν_0 a distribution on ℝ^d, so by §2.3 with a positive C¹ density → ν₀ an arbitrary probability measure on ℝ^d; reason: a law with a positive C¹ density is in particular a probability measure, so the Lean statement specializes to the source's; the paper's proof (data processing for TV) does not use the density
--   - encoding: p a distribution on ℝ^d with positive C¹ density, p_t = Law(e^{−t}Z_0 + √(1 − e^{−2t})G), ∇log p_t → p = densMeasure ρ with IsRegDensity ρ; p_t = ouMarginal ρ t, the law with the explicit Gaussian-convolution density ouDensity ρ t (ρ at t = 0); ∇log p_t = ouScore ρ t, the gradient of the log of that density; reason: §2.3 makes every distribution have a positive C¹ density; the convolution is the density of e^{−t}Z_0 + √(1 − e^{−2t})G
--   - encoding: solutions of the learned reverse SDE (2.2) and their law p̂_T → every probability space Ω : Type, every B with EthierKurtz.IsStandardBrownian P B, every Y with IsSDESolution P (learnedReverseDrift ŝ T) B T Y, P.map (Y 0) = ν₀ and Y 0 independent of B; E_{p̂_T} f = ∫ f(Y_T) dP; reason: additive noise: the pathwise integral equation is the SDE; the bound holds for every solution
--   - encoding: Assumption 2.1: E_{p_t}‖ŝ_t − ∇log p_t‖² ≤ ε²_score for 0 < t < T → ε ≥ 0 and, for every t ∈ (0, T), ∫⁻ ‖ŝ x t − ouScore ρ t x‖² d p_t ≤ ε²; reason: a lower Lebesgue integral, never a default value
--   - encoding: §2.3 standing assumptions: d ≥ 1, T > 0; ∇log p_t and ŝ_t Lipschitz in x uniformly in t and continuous in (x, t); f uniformly continuous and C² → hypotheses hd, hT, hscore, hsHat (IsLipContDrift on ℝ^d × [0, T]), hfu, hf2; reason: standing assumptions as binders; measurability and square-integrability of f follow from uniform continuity and 0 ≤ f ≤ 1
--   - encoding: C_f = max(C_P(p; f), 1) ∈ [1, ∞] and the term 2ε_score√(1 + log C_f) → hypothesis ε = 0 ∨ C_P(p; f) ≠ ∞, and C_f = max(C_P(p; f).toReal, 1) ∈ ℝ; reason: when ε_score > 0 and C_P(p; f) = ∞ the right side is +∞ and the bound is trivial; only that case is excluded
--   - reading: 2ε_score√(1 + log C_f) when ε_score = 0 and C_P(p; f) = ∞ (0 · ∞, not defined by the source) → 0; reason: the convention 0 · ∞ = 0; it keeps the exact-score case (|E_{p̂_T} f − E_p f| ≤ η_T) in the statement
-- source:
--   Giapitzakis, Moitra, Risteski, Rohatgi, Error accumulation in reverse diffusion with an imperfect score: beyond path-space analyses, STOC 2027 submission (manuscript sha256 c0118fd2…), p. 23, Theorem B.1, (B.2); setting §2.1–§2.3, pp. 8–10 (Assumption 2.1, (2.1), (2.2), (2.3), Definition 2.4)

import Mathlib
import Definitions.Def_DiffusionErrorAcc_Stability_TransportEnergy
import Definitions.Def_DiffusionErrorAcc_Stability_OUMarginal
import Definitions.Def_DiffusionErrorAcc_Stability_AdditiveSDE

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DiffusionErrorAcc.Stability

/-- Theorem B.1 (p. 23). Fix `d ≥ 1`, `T > 0` and a ground-truth law `p = ρ dx` with positive `C¹`
density, OU marginals `p_t` and true score `∇ log p_t` (Lipschitz in space uniformly in
`t ∈ [0, T]`, jointly continuous). Let `ŝ` be a learned score with the same regularity and
`E_{p_t} ‖ŝ_t − ∇ log p_t‖² ≤ ε²_score` for `0 < t < T` (Assumption 2.1). Let `f : ℝ^d → [0, 1]` be
a test statistic (uniformly continuous, `C²`) with `Var_p(f) > 0`, `C_f = max(C_P(p; f), 1)`.
Then for every initial law `ν_0`, every standard Brownian motion `B` and every solution `Y` of the
learned reverse SDE (2.2) `dY_u = (Y_u + 2 ŝ_{T−u}(Y_u)) du + √2 dB_u`, `Y_0 ∼ ν_0` independent of
`B`, the output law `p̂_T = Law(Y_T)` satisfies
`|E_{p̂_T} f − E_p f| ≤ η_T + 2 ε_score √(1 + log C_f) + ε²_score T`, `η_T = TV(ν_0, p_T)`.
(When `ε_score > 0` and `C_P(p; f) = ∞` the right side is `+∞`; that case is excluded.) -/
theorem theorem_B_1 {d : ℕ} (hd : 1 ≤ d) {T : ℝ} (hT : 0 < T)
    (ρ : Rd d → ℝ) (hρ : IsRegDensity ρ)
    (hscore : IsLipContDrift (fun x t => ouScore ρ t x) T)
    (sHat : Rd d → ℝ → Rd d) (hsHat : IsLipContDrift sHat T)
    (εscore : ℝ) (hε : 0 ≤ εscore)
    (hA21 : ∀ t ∈ Ioo (0 : ℝ) T,
      ∫⁻ x, ‖sHat x t - ouScore ρ t x‖ₑ ^ 2 ∂(ouMarginal ρ t) ≤ ENNReal.ofReal (εscore ^ 2))
    (ν₀ : Measure (Rd d)) [IsProbabilityMeasure ν₀]
    (f : Rd d → ℝ) (hf : ∀ x, f x ∈ Icc (0 : ℝ) 1) (hfu : UniformContinuous f)
    (hf2 : ContDiff ℝ 2 f) (hvar : 0 < variance f (densMeasure ρ))
    (hfin : εscore = 0 ∨ poincareConstF ρ f ≠ ∞)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Rd d) (hB : EthierKurtz.IsStandardBrownian P B)
    (Y : ℝ → Ω → Rd d) (hY : IsSDESolution P (learnedReverseDrift sHat T) B T Y)
    (hY0 : P.map (Y 0) = ν₀) (hind : IndepFun (Y 0) (fun ω t => B t ω) P) :
    |(∫ ω, f (Y T ω) ∂P) - ∫ x, f x ∂(densMeasure ρ)| ≤
      tvDist ν₀ (ouMarginal ρ T) +
        2 * εscore * Real.sqrt (1 + Real.log (max (poincareConstF ρ f).toReal 1)) +
        εscore ^ 2 * T := by sorry

end DiffusionErrorAcc.Stability
