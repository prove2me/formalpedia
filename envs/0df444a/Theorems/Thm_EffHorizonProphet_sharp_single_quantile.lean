-- Prove2me | Theorems.Thm_EffHorizonProphet_sharp_single_quantile
-- name    : EffHorizonProphet.sharp_single_quantile
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:46:27.596372+00:00
-- url     : https://prove2.me/theorems/50cc184d-12d5-40a8-9070-bbd7bdae1345
-- title:
--   Theorems 1 and 6 — acceptance probability $1/B$ attains the optimal asymptotic ratio of single-quantile policies
-- statement:
--   Fix $S\ge1$ and a common decay factor $\tilde\gamma\in[0,1]$, with equal-length phases as $n\to\infty$, and let
--   $$U(S,\tilde\gamma)=\begin{cases}\dfrac{\big(1-\tilde\gamma^Se^{-Sr}\big)\big(1-e^{-r}\big)}{1-\tilde\gamma e^{-r}},&0\le\tilde\gamma<1,\ r=\dfrac{1-\tilde\gamma}{1-\tilde\gamma^S},\\[1ex]1-\dfrac1e,&\tilde\gamma=1.\end{cases}$$
--   Then:
--
--   1. (Theorem 1) every sequence of single-quantile threshold policies, even with the threshold and tie-break chosen from the known base law, has $\limsup_{n\to\infty}\mathrm{CR}_n(\tau)\le U(S,\tilde\gamma)$;
--   2. (Remark 5) a policy with per-stage acceptance probability exactly $1/B$, where $B=\sum_sn_s\tilde\gamma^{s-1}$ is the effective horizon, exists on all admissible laws, including those with atoms;
--   3. (Theorem 6) every such policy has $\liminf_{n\to\infty}\mathrm{CR}_n(\tau)\ge U(S,\tilde\gamma)$.
--
--   So the acceptance probability $1/B$, determined only by the phase profile, attains the optimum among single-quantile policies, and the deterioration from $1-1/e$ towards $1/2$ as $S$ grows and $\tilde\gamma\uparrow1$ cannot be improved within this class.
--
--   Differences from the source:
--   - generalization: phases of equal length $n/S$ with $S\mid n$ and $n\to\infty$ → any sequence of profiles $L_t$ with $n_t=\sum_s L_t(s)\to\infty$ and $L_t(s)/n_t\to 1/S$; reason: this is the reading "(or asymptotically $n_s/n\to 1/S$)" of p.3 and contains the printed case $L_t\equiv t$, for which a sanity lemma checks the hypotheses
--   - reading: $\tau$ is a stopping time for the filtration of $(X_i)$ (p.3), while Remarks 5 and 16 add randomized tie-breaking with coins $U_i$ → the coins are coordinates of the sample space and $\tau$ is a stopping time for $(Y_i,U_i)$; reason: Remark 16 introduces the coins this way, and the proof on p.21 uses them to reach every acceptance probability $p$
--   - reading: "any single-quantile threshold stopping policy $\tau$" → a rule chosen as a function of $t$ and of the base law; reason: the class claimed on p.2: "even among single-quantile policies that may choose their acceptance probability using the known base distribution"
--   - encoding: acceptance is $X_i>\alpha_s$ with $\alpha_s=\tilde\gamma^{s-1}\alpha_1$ → acceptance is $Y_i>\alpha_1$, in the base scale; reason: the events coincide for $\tilde\gamma>0$; at $\tilde\gamma=0$ they differ only in phases $s\ge2$, where the reward is $0$ either way (footnote 3, p.8)
--   - encoding: phases and stages are numbered from $1$ → they are numbered from $0$; reason: a relabelling: paper phase $s$ is Lean phase $s-1$
--   - encoding: $\limsup_{n\to\infty}\mathrm{CR}_n(\tau)\le U$ → $\forall u>U$, eventually $\mathrm{cr}<u$; reason: the same statement for a sequence bounded in $[0,1]$, without the junk values of a real limsup
--   - encoding: $\liminf_{n\to\infty}\mathrm{CR}_n(\tau)\ge U$ → $\forall u<U$, eventually $u<\mathrm{cr}$; reason: the same statement for a sequence bounded in $[0,1]$, without the junk values of a real liminf
--   - encoding: the policy with $p_n=0$ (p.21) → the threshold $\alpha=\top$; reason: no finite threshold has acceptance probability $0$ for an unbounded law
--   - encoding: Algorithm 1 with $\alpha_1$ from (6), $P(Y>\alpha_1)=a/n$, and Remark 5 → any family of rules with acceptance probability exactly $1/B$, $B=\sum_s L_t(s)\tilde\gamma^{s-1}$, at every admissible law once $B\ge1$; reason: at the printed profile $1/B=a/n$; rules with this acceptance probability differ only on null sets; the proof uses $B\ge1$ in (39), and it holds eventually
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Theorem 1, pp.4–5; Theorem 6, p.9; statement of the combination, p.2 and p.10

import Mathlib
import Definitions.Def_EffHorizonProphet_IsEqualProfile
import Definitions.Def_EffHorizonProphet_cr
import Definitions.Def_EffHorizonProphet_Calibrated
import Definitions.Def_EffHorizonProphet_optRatio

open MeasureTheory Filter

namespace EffHorizonProphet

/-- **Theorems 1 and 6 combined** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), pp.4–5, p.9, p.10; statement of the contribution, p.2):
the acceptance probability `1/B`, determined only by the phase profile, attains the optimal
asymptotic competitive ratio `U(S, γ̃)` of single-quantile threshold policies, even among policies
that choose their acceptance probability using the known base distribution. For every `S ≥ 1`,
`γ̃ ∈ [0, 1]` and asymptotically equal profile:

1. (Theorem 1) every family of rules has `limsup CR_n ≤ U(S, γ̃)`;
2. (Remark 5) a family of rules with acceptance probability `1/B` exists, on all admissible laws
   including those with atoms;
3. (Theorem 6) every such family has `liminf CR_n ≥ U(S, γ̃)`.

**Formalization Note** Phases and stages are `0`-based, with `n = ∑ s, L t s`; the printed `n_s = n/S`
is `L t = fun _ => t`. A `Rule` is a threshold in `[0, ∞]` in the base scale plus a tie-breaking
probability, with its coin in the sample space. `limsup ≤ U` and `liminf ≥ U` are stated as
`∀ u > U, ∀ᶠ t, cr < u` and `∀ u < U, ∀ᶠ t, u < cr`. -/
theorem sharp_single_quantile {S : ℕ} (hS : 1 ≤ S) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    {L : ℕ → Fin S → ℕ} (hL : IsEqualProfile L) :
    (∀ π : ℕ → Measure ℝ → Rule, ∀ u, optRatio S γ < u →
        ∀ᶠ t in atTop, cr γ (L t) (π t) < u) ∧
      (∃ π : ℕ → Measure ℝ → Rule, Calibrated γ L π) ∧
      (∀ π : ℕ → Measure ℝ → Rule, Calibrated γ L π → ∀ u, u < optRatio S γ →
        ∀ᶠ t in atTop, u < cr γ (L t) (π t)) := by sorry

end EffHorizonProphet
