-- Prove2me | Theorems.Thm_EffHorizonProphet_Supplement_theorem_19
-- name    : EffHorizonProphet.Supplement.theorem_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:08:22.150839+00:00
-- url     : https://prove2.me/theorems/453b0ee4-d6e5-4361-b315-68291ce4236e
-- title:
--   Theorem 19 — every law-independent single-threshold rule has $\limsup\mathrm{CR}_n\le\sum_s\Gamma_{s-1}e^{-\Lambda_{s-1}/C_S}(1-e^{-\lambda_s/C_S})$
-- statement:
--   Let $S\ge1$, decay factors $\gamma_1,\dots,\gamma_{S-1}\in[0,1]$ with $\Gamma_0=1$, $\Gamma_s=\prod_{t\le s}\gamma_t$, and phase proportions $\lambda_1,\dots,\lambda_S\in(0,1]$ with $\sum_s\lambda_s=1$, in the model of Theorem 18 ($X_i=\Gamma_{s-1}Y_i$, $n\to\infty$, $n_s/n\to\lambda_s$). For any single-threshold stopping policy $\tau$ whose acceptance quantile is fixed independently of the base distribution,
--   $$\limsup_{n\to\infty}\mathrm{CR}_n(\tau)\ \le\ \sum_{s=1}^{S}\Gamma_{s-1}\exp\Big(-\frac{\Lambda_{s-1}}{C_S}\Big)\Big(1-\exp\Big(-\frac{\lambda_s}{C_S}\Big)\Big),$$
--   with $\Lambda_{s-1}=\sum_{t<s}\lambda_t$ and $C_S=\sum_t\Gamma_{t-1}\lambda_t$.
--
--   A single-threshold policy accepts at every stage with the same probability $p_n$ (base threshold $\alpha$, threshold $\Gamma_{s-1}\alpha$ in phase $s$, randomized ties); $p_n$ may depend on the horizon but not on the law. Together with Theorem 18 this shows that the calibration $1/B_G$ is optimal in this class.
--
--   Differences from the source:
--   - encoding: decay factors $(\gamma_s)_{s=1}^{S-1}\in[0,1]^{S-1}$ → a sequence $g$ with $g(t)=\gamma_{t+1}$ and $0\le g(t)\le1$ for $t+1<S$; reason: the values $g(t)$, $t\ge S-1$, are never used
--   - encoding: $(\lambda_s)\in(0,1]^S$ with $\sum_s\lambda_s=1$, and $S\ge1$ → $\lambda_s>0$ and $\sum_s\lambda_s=1$; reason: $\lambda_s\le1$ and $S\ge1$ follow from these two conditions
--   - encoding: $n\to\infty$ with $n_s/n\to\lambda_s$ → a sequence of profiles $L_t$ with $\sum_sL_t(s)\to\infty$ and $L_t(s)/\sum_{s'}L_t(s')\to\lambda_s$; reason: the paper's limit, written along a sequence of profiles
--   - reading: "any single-threshold stopping policy $\tau$ with a fixed acceptance quantile independent of the base distribution" → a family of rules (base threshold, tie-break) indexed by the horizon, with a sequence $p_t$ such that the acceptance probability at every admissible law is $p_t$; reason: A.8 parametrizes the policy by its per-stage acceptance probability $p$, and Lemma 20 treats sequences $p_n$
--   - encoding: the policy with $p=0$ → the threshold $\alpha=\top$; reason: no finite threshold has acceptance probability $0$ for an unbounded law
--   - encoding: acceptance $X_i>\alpha_s$ with $\alpha_s=\Gamma_{s-1}\alpha_1$, thresholds chosen only in phases with $\Gamma_{s-1}>0$ (48) → acceptance $Y_i>\alpha_1$ (or a tie with $U_i\le\theta$) in the base scale, in every phase; reason: the events coincide when $\Gamma_{s-1}>0$; once $\Gamma_{s-1}=0$ every later reward is $0$, so stopping pays $0$ either way (footnote 5, p.35)
--   - reading: $\tau$ is a stopping time for the filtration of $(X_i)$ (p.3), while Remark 16 adds randomized tie-breaking with coins $U_i$ → the coins are coordinates of the sample space; reason: Remark 16 introduces the coins this way; A.7 refers to it for laws with atoms
--   - encoding: $\limsup_{n\to\infty}\mathrm{CR}_n(\tau)\le R$ → $\forall u>R$, eventually $\mathrm{CR}<u$; reason: the same statement for a sequence in $[0,1]$, without the junk values of a real limsup
--   - encoding: phases and stages are numbered from $1$ → they are numbered from $0$; reason: a relabelling: paper stage $i$ is Lean stage $i-1$
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Theorem 19, p.36; proof in A.8, pp.38–45

import Mathlib
import Definitions.Def_EffHorizonProphet_IsAdmissible
import Definitions.Def_EffHorizonProphet_acceptProb
import Definitions.Def_EffHorizonProphet_Supplement_generalRatio
import Definitions.Def_EffHorizonProphet_Supplement_crG
import Definitions.Def_EffHorizonProphet_Supplement_IsPropProfile

open MeasureTheory Filter

namespace EffHorizonProphet.Supplement

/-- **Theorem 19** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), p.36; proof in A.8, pp.38–45): fix `S ≥ 1`, decay factors
`(γ_s)_{s=1}^{S−1} ∈ [0, 1]^{S−1}` and phase proportions `(λ_s)_{s=1}^{S} ∈ (0, 1]^S` with
`∑ λ_s = 1`. For any single-threshold stopping policy `τ` with a fixed acceptance quantile
independent of the base distribution,
`limsup_{n→∞} CR_n(τ) ≤ ∑_s Γ_{s−1} exp(−Λ_{s−1}/C_S)(1 − exp(−λ_s/C_S))`.

**Formalization Note** The decay factors are `g t` (paper `γ_{t+1}`) for `t + 1 < S`. A policy is a
family of rules (base threshold in `[0, ∞]`, tie-break) whose acceptance probability `p_n` is the same
for every admissible law; it may vary with `n` (as in Lemma 20) and may be `0` (`α = ⊤`).
"limsup ≤ R" is `∀ u > R, ∀ᶠ t, CR < u`. The profile is any sequence with `n → ∞` and
`n_s/n → λ_s`. -/
theorem theorem_19 {S : ℕ} {g : ℕ → ℝ} (hg0 : ∀ t, t + 1 < S → 0 ≤ g t)
    (hg1 : ∀ t, t + 1 < S → g t ≤ 1) {lam : Fin S → ℝ} (hlam : ∀ s, 0 < lam s)
    (hlam1 : ∑ s, lam s = 1) {L : ℕ → Fin S → ℕ} (hL : IsPropProfile lam L)
    (π : ℕ → Measure ℝ → Rule)
    (hπ : ∃ p : ℕ → ℝ, ∀ t D, IsAdmissible D → acceptProb D (π t D) = p t)
    {u : ℝ} (hu : generalRatio g lam < u) :
    ∀ᶠ t in atTop, crG g (L t) (π t) < u := by sorry

end EffHorizonProphet.Supplement
