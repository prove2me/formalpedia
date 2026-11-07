-- Prove2me | Theorems.Thm_EffHorizonProphet_theorem_1
-- name    : EffHorizonProphet.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:46:14.594128+00:00
-- url     : https://prove2.me/theorems/73440be6-fca9-4a95-be18-c2e18b1eb974
-- title:
--   Theorem 1 — upper bound for every single-quantile policy
-- statement:
--   Assume a common decay factor $\tilde\gamma\in[0,1]$ and equal-length phases, $S\ge1$. For any single-quantile threshold stopping policy $\tau$,
--   $$\limsup_{n\to\infty}\mathrm{CR}_n(\tau)\le U(S,\tilde\gamma)=\begin{cases}\dfrac{\big(1-\tilde\gamma^Se^{-Sr}\big)\big(1-e^{-r}\big)}{1-\tilde\gamma e^{-r}},&0\le\tilde\gamma<1,\ r=\dfrac{1-\tilde\gamma}{1-\tilde\gamma^S},\\[1ex]1-\dfrac1e,&\tilde\gamma=1.\end{cases}$$
--
--   The policy may select a different threshold and tie-break for each horizon and for each base law. Accumulated discounting thus moves the single-quantile guarantee below the classical value $1-1/e$ in the interior of the decay range.
--
--   Differences from the source:
--   - generalization: phases of equal length $n/S$ with $S\mid n$ and $n\to\infty$ → any sequence of profiles $L_t$ with $n_t=\sum_s L_t(s)\to\infty$ and $L_t(s)/n_t\to 1/S$; reason: this is the reading "(or asymptotically $n_s/n\to 1/S$)" of p.3 and contains the printed case $L_t\equiv t$, for which a sanity lemma checks the hypotheses
--   - reading: $\tau$ is a stopping time for the filtration of $(X_i)$ (p.3), while Remarks 5 and 16 add randomized tie-breaking with coins $U_i$ → the coins are coordinates of the sample space and $\tau$ is a stopping time for $(Y_i,U_i)$; reason: Remark 16 introduces the coins this way, and the proof on p.21 uses them to reach every acceptance probability $p$
--   - reading: "any single-quantile threshold stopping policy $\tau$" → a rule chosen as a function of $t$ and of the base law; reason: the class claimed on p.2: "even among single-quantile policies that may choose their acceptance probability using the known base distribution"
--   - encoding: acceptance is $X_i>\alpha_s$ with $\alpha_s=\tilde\gamma^{s-1}\alpha_1$ → acceptance is $Y_i>\alpha_1$, in the base scale; reason: the events coincide for $\tilde\gamma>0$; at $\tilde\gamma=0$ they differ only in phases $s\ge2$, where the reward is $0$ either way (footnote 3, p.8)
--   - encoding: phases and stages are numbered from $1$ → they are numbered from $0$; reason: a relabelling: paper phase $s$ is Lean phase $s-1$
--   - encoding: $\limsup_{n\to\infty}\mathrm{CR}_n(\tau)\le U$ → $\forall u>U$, eventually $\mathrm{cr}<u$; reason: the same statement for a sequence bounded in $[0,1]$, without the junk values of a real limsup
--   - encoding: the policy with $p_n=0$ (p.21) → the threshold $\alpha=\top$; reason: no finite threshold has acceptance probability $0$ for an unbounded law
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Theorem 1, pp.4–5

import Mathlib
import Definitions.Def_EffHorizonProphet_IsEqualProfile
import Definitions.Def_EffHorizonProphet_cr
import Definitions.Def_EffHorizonProphet_optRatio

open MeasureTheory Filter

namespace EffHorizonProphet

/-- **Theorem 1** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), pp.4–5): for any single-quantile threshold stopping policy `τ`,
`limsup_{n→∞} CR_n(τ) ≤ U(S, γ̃)`, the right-hand side being `optRatio S γ`.

**Formalization Note** The family `π` is arbitrary: a rule for each `t` and each base law, with any
threshold and tie-break, including `α = ⊤`. "limsup ≤ U" is `∀ u > U, ∀ᶠ t, cr < u`, which avoids
the junk values of a real `limsup`. The profile generalizes `n_s = n/S`, which is the case
`L t = fun _ => t`. -/
theorem theorem_1 {S : ℕ} (hS : 1 ≤ S) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    {L : ℕ → Fin S → ℕ} (hL : IsEqualProfile L) (π : ℕ → Measure ℝ → Rule) {u : ℝ}
    (hu : optRatio S γ < u) :
    ∀ᶠ t in atTop, cr γ (L t) (π t) < u := by sorry

end EffHorizonProphet
