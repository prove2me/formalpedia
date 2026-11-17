-- Prove2me | Theorems.Thm_EffHorizonProphet_Supplement_theorem_18
-- name    : EffHorizonProphet.Supplement.theorem_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:07:24.411708+00:00
-- url     : https://prove2.me/theorems/9e8fae1e-88d8-4dfc-b04f-ca85f460379e
-- title:
--   Theorem 18 — the $1/B_G$ rule has $\liminf\mathrm{CR}_n\ge\sum_s\Gamma_{s-1}e^{-\Lambda_{s-1}/C_S}(1-e^{-\lambda_s/C_S})$ under general decay and proportions
-- statement:
--   Let $S\ge1$, let $\gamma_1,\dots,\gamma_{S-1}\in[0,1]$ be decay factors with cumulative scales $\Gamma_0=1$, $\Gamma_s=\prod_{t\le s}\gamma_t$, and let $\lambda_1,\dots,\lambda_S\in(0,1]$ with $\sum_s\lambda_s=1$. Rewards are $X_i=\Gamma_{s-1}Y_i$ for $i$ in phase $s$, with $Y_i$ i.i.d. from an admissible law, and the phase lengths satisfy $n\to\infty$, $n_s/n\to\lambda_s$. Put $\Lambda_{s-1}=\sum_{t<s}\lambda_t$, $C_S=\sum_t\Gamma_{t-1}\lambda_t$ and $B_G=\sum_s\Gamma_{s-1}n_s$.
--
--   If Algorithm 1 uses a base threshold with per-stage acceptance probability $\tilde a/n=1/B_G$ (the calibration (48), with randomized tie-breaking for atoms), then
--   $$\liminf_{n\to\infty}\mathrm{CR}_n(\tau)\ \ge\ \sum_{s=1}^{S}\Gamma_{s-1}\exp\Big(-\frac{\Lambda_{s-1}}{C_S}\Big)\Big(1-\exp\Big(-\frac{\lambda_s}{C_S}\Big)\Big).$$
--   The bound is uniform over admissible laws, which may have atoms and unbounded support. With a common decay factor and $\lambda_s=1/S$ it is Theorem 6.
--
--   Differences from the source:
--   - encoding: decay factors $(\gamma_s)_{s=1}^{S-1}\in[0,1]^{S-1}$ → a sequence $g$ with $g(t)=\gamma_{t+1}$ and $0\le g(t)\le1$ for $t+1<S$; reason: the values $g(t)$, $t\ge S-1$, are never used
--   - encoding: $(\lambda_s)\in(0,1]^S$ with $\sum_s\lambda_s=1$, and $S\ge1$ → $\lambda_s>0$ and $\sum_s\lambda_s=1$; reason: $\lambda_s\le1$ and $S\ge1$ follow from these two conditions
--   - encoding: $n\to\infty$ with $n_s/n\to\lambda_s$ → a sequence of profiles $L_t$ with $\sum_sL_t(s)\to\infty$ and $L_t(s)/\sum_{s'}L_t(s')\to\lambda_s$; reason: the paper's limit, written along a sequence of profiles
--   - encoding: Algorithm 1 with $\alpha_1$ from (48), $P(\Gamma_{s-1}Y>\alpha_s)=\tilde a/n$, and Remark 16 for atoms → any family of rules whose acceptance probability at every admissible law is exactly $1/B_G$ whenever $B_G\ge1$; reason: (48) states $\tilde a/n=1/B_G$; rules with this acceptance probability differ only on null sets; $B_G\ge1$ makes $1/B_G$ a probability and holds eventually since $B_G/n\to C_S>0$
--   - encoding: acceptance $X_i>\alpha_s$ with $\alpha_s=\Gamma_{s-1}\alpha_1$, thresholds chosen only in phases with $\Gamma_{s-1}>0$ (48) → acceptance $Y_i>\alpha_1$ (or a tie with $U_i\le\theta$) in the base scale, in every phase; reason: the events coincide when $\Gamma_{s-1}>0$; once $\Gamma_{s-1}=0$ every later reward is $0$, so stopping pays $0$ either way (footnote 5, p.35)
--   - reading: $\tau$ is a stopping time for the filtration of $(X_i)$ (p.3), while Remark 16 adds randomized tie-breaking with coins $U_i$ → the coins are coordinates of the sample space; reason: Remark 16 introduces the coins this way; A.7 refers to it for laws with atoms
--   - encoding: $\liminf_{n\to\infty}\mathrm{CR}_n(\tau)\ge R$ → $\forall u<R$, eventually $u<\mathrm{CR}$; reason: the same statement for a sequence in $[0,1]$, without the junk values of a real liminf
--   - encoding: phases and stages are numbered from $1$ → they are numbered from $0$; reason: a relabelling: paper stage $i$ is Lean stage $i-1$
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Theorem 18, p.35; Eq. (48), p.35; proof in A.7, pp.36–38

import Mathlib
import Definitions.Def_EffHorizonProphet_IsAdmissible
import Definitions.Def_EffHorizonProphet_acceptProb
import Definitions.Def_EffHorizonProphet_Supplement_effHorizonG
import Definitions.Def_EffHorizonProphet_Supplement_generalRatio
import Definitions.Def_EffHorizonProphet_Supplement_crG
import Definitions.Def_EffHorizonProphet_Supplement_IsPropProfile

open MeasureTheory Filter

namespace EffHorizonProphet.Supplement

/-- **Theorem 18** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), p.35; proof in A.7, pp.36–38): in the decaying-reward model with `S ≥ 1`
phases, decay factors `(γ_s)_{s=1}^{S−1} ∈ [0, 1]^{S−1}` and phase proportions
`(λ_s)_{s=1}^{S} ∈ (0, 1]^S` with `∑ λ_s = 1`, Algorithm 1 with threshold `α_1` from (48) satisfies
`liminf_{n→∞} CR_n(τ) ≥ ∑_s Γ_{s−1} exp(−Λ_{s−1}/C_S)(1 − exp(−λ_s/C_S))`.

**Formalization Note** The decay factors are `g t` (paper `γ_{t+1}`) for `t + 1 < S`. The policy is any
family whose acceptance probability at every admissible law is `ã/n = 1/B_G` ((48)), whenever
`B_G ≥ 1` (so that `1/B_G` is a probability; this holds eventually). "liminf ≥ R" is
`∀ u < R, ∀ᶠ t, u < CR`, uniform in the law because the infimum sits inside `crG`. The profile is
any sequence with `n → ∞` and `n_s/n → λ_s`. -/
theorem theorem_18 {S : ℕ} {g : ℕ → ℝ} (hg0 : ∀ t, t + 1 < S → 0 ≤ g t)
    (hg1 : ∀ t, t + 1 < S → g t ≤ 1) {lam : Fin S → ℝ} (hlam : ∀ s, 0 < lam s)
    (hlam1 : ∑ s, lam s = 1) {L : ℕ → Fin S → ℕ} (hL : IsPropProfile lam L)
    (π : ℕ → Measure ℝ → Rule)
    (hπ : ∀ t D, IsAdmissible D → 1 ≤ effHorizonG g (L t) →
      acceptProb D (π t D) = 1 / effHorizonG g (L t))
    {u : ℝ} (hu : u < generalRatio g lam) :
    ∀ᶠ t in atTop, u < crG g (L t) (π t) := by sorry

end EffHorizonProphet.Supplement
