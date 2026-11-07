-- Prove2me | Theorems.Thm_EffHorizonProphet_theorem_6
-- name    : EffHorizonProphet.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:46:20.603518+00:00
-- url     : https://prove2.me/theorems/076fd91b-7da4-49d7-92cc-d697e964ad85
-- title:
--   Theorem 6 — Algorithm 1 achieves the bound
-- statement:
--   Consider $S\ge1$ phases of equal length $n/S$ and a common decay factor $\tilde\gamma\in[0,1]$. The stopping policy of Algorithm 1 with $\alpha_1$ from (6), that is with acceptance probability $a/n=1/B$, achieves
--   $$\liminf_{n\to\infty}\mathrm{CR}_n(\tau)\ge U(S,\tilde\gamma).$$
--
--   The guarantee is uniform in the base law because the competitive ratio is already the infimum over all admissible laws, and the bound holds for laws with atoms by the tie-breaking of Remark 5.
--
--   Differences from the source:
--   - generalization: phases of equal length $n/S$ with $S\mid n$ and $n\to\infty$ → any sequence of profiles $L_t$ with $n_t=\sum_s L_t(s)\to\infty$ and $L_t(s)/n_t\to 1/S$; reason: this is the reading "(or asymptotically $n_s/n\to 1/S$)" of p.3 and contains the printed case $L_t\equiv t$, for which a sanity lemma checks the hypotheses
--   - encoding: Algorithm 1 with $\alpha_1$ from (6), $P(Y>\alpha_1)=a/n$, and Remark 5 → any family of rules with acceptance probability exactly $1/B$, $B=\sum_s L_t(s)\tilde\gamma^{s-1}$, at every admissible law once $B\ge1$; reason: at the printed profile $1/B=a/n$; rules with this acceptance probability differ only on null sets; the proof uses $B\ge1$ in (39), and it holds eventually
--   - reading: $\tau$ is a stopping time for the filtration of $(X_i)$ (p.3), while Remarks 5 and 16 add randomized tie-breaking with coins $U_i$ → the coins are coordinates of the sample space and $\tau$ is a stopping time for $(Y_i,U_i)$; reason: Remark 16 introduces the coins this way, and the proof on p.21 uses them to reach every acceptance probability $p$
--   - encoding: acceptance is $X_i>\alpha_s$ with $\alpha_s=\tilde\gamma^{s-1}\alpha_1$ → acceptance is $Y_i>\alpha_1$, in the base scale; reason: the events coincide for $\tilde\gamma>0$; at $\tilde\gamma=0$ they differ only in phases $s\ge2$, where the reward is $0$ either way (footnote 3, p.8)
--   - encoding: phases and stages are numbered from $1$ → they are numbered from $0$; reason: a relabelling: paper phase $s$ is Lean phase $s-1$
--   - encoding: $\liminf_{n\to\infty}\mathrm{CR}_n(\tau)\ge U$ → $\forall u<U$, eventually $u<\mathrm{cr}$; reason: the same statement for a sequence bounded in $[0,1]$, without the junk values of a real liminf
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Theorem 6, p.9; Eq. (42), p.30

import Mathlib
import Definitions.Def_EffHorizonProphet_IsEqualProfile
import Definitions.Def_EffHorizonProphet_cr
import Definitions.Def_EffHorizonProphet_Calibrated
import Definitions.Def_EffHorizonProphet_optRatio

open MeasureTheory Filter

namespace EffHorizonProphet

/-- **Theorem 6** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), p.9), with Eq. (42), p.30: the stopping policy of Algorithm 1 with `α₁` from
(6) achieves `liminf_{n→∞} CR_n(τ) ≥ U(S, γ̃)`, the right-hand side being `optRatio S γ`.

**Formalization Note** The policy is any `Calibrated` family (Remark 5 makes it well defined on
atoms). "liminf ≥ U" is `∀ u < U, ∀ᶠ t, u < cr`. The bound is uniform in the law because the
infimum sits inside `cr`. The profile generalizes `n_s = n/S`, which is the case
`L t = fun _ => t`. -/
theorem theorem_6 {S : ℕ} (hS : 1 ≤ S) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    {L : ℕ → Fin S → ℕ} (hL : IsEqualProfile L) (π : ℕ → Measure ℝ → Rule)
    (hπ : Calibrated γ L π) {u : ℝ} (hu : u < optRatio S γ) :
    ∀ᶠ t in atTop, u < cr γ (L t) (π t) := by sorry

end EffHorizonProphet
