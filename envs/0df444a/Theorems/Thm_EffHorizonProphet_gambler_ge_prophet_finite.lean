-- Prove2me | Theorems.Thm_EffHorizonProphet_gambler_ge_prophet_finite
-- name    : EffHorizonProphet.gambler_ge_prophet_finite
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:44:50.283463+00:00
-- url     : https://prove2.me/theorems/b1643d99-9a42-4e97-a2e1-2057ddda94bf
-- title:
--   Eq. (10) and (41) — nonasymptotic lower bound
-- statement:
--   Let $D$ be admissible and suppose the effective horizon satisfies $B\ge1$. For a rule with acceptance probability $1/B$, and with $q=1-1/B$ and $N_s=\sum_{r<s}n_r$,
--   $$\mathbb E[X_\tau]\ge\Big(\sum_{s=1}^S\tilde\gamma^{\,s-1}q^{N_s}\big(1-q^{n_s}\big)\Big)\,\mathbb E\Big[\max_{i\in[n]}X_i\Big].$$
--
--   The bound is nonasymptotic and uniform in $D$. Letting $n\to\infty$ gives Theorem 6.
--
--   Differences from the source:
--   - generalization: equal phases $n_s=n/S$, in (10) → arbitrary phase lengths; reason: at $L\equiv m$ this is (10) exactly; for general lengths it has the shape of (57), p.38
--   - reading: the exponents "$(n/S)+O(1)$" in (41) → exact exponents $N_s$ and $L(s)$; reason: (41) is an inexact rendering of (36); the page itself prints (10) and (57) with exact exponents
--   - encoding: $1-a/n$ and $P(Y>\alpha_1)=a/n$ → $q=1-1/B$ and acceptance probability $1/B$, with the guard $B\ge1$; reason: at equal phases $a/n=1/B$
--   - reading: $\tau$ is a stopping time for the filtration of $(X_i)$ (p.3), while Remarks 5 and 16 add randomized tie-breaking with coins $U_i$ → the coins are coordinates of the sample space and $\tau$ is a stopping time for $(Y_i,U_i)$; reason: Remark 16 introduces the coins this way, and the proof on p.21 uses them to reach every acceptance probability $p$
--   - encoding: acceptance is $X_i>\alpha_s$ with $\alpha_s=\tilde\gamma^{s-1}\alpha_1$ → acceptance is $Y_i>\alpha_1$, in the base scale; reason: the events coincide for $\tilde\gamma>0$; at $\tilde\gamma=0$ they differ only in phases $s\ge2$, where the reward is $0$ either way (footnote 3, p.8)
--   - encoding: phases and stages are numbered from $1$ → they are numbered from $0$; reason: a relabelling: paper phase $s$ is Lean phase $s-1$
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Eq. (10), p.10; Eq. (41), p.30; shape of (57), p.38

import Mathlib
import Definitions.Def_EffHorizonProphet_IsAdmissible
import Definitions.Def_EffHorizonProphet_gambler
import Definitions.Def_EffHorizonProphet_prophet
import Definitions.Def_EffHorizonProphet_effHorizon
import Definitions.Def_EffHorizonProphet_acceptProb

open MeasureTheory

namespace EffHorizonProphet

/-- **Eq. (10) and (41)** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), p.10 and p.30): nonasymptotically and uniformly in the admissible
law, a rule with acceptance probability `1/B` satisfies
`E[X_τ] ≥ (∑_s γ̃^{s-1} q^{N_s} (1 - q^{n_s})) E[max_i X_i]`, where `q = 1 - 1/B` and
`N_s = ∑_{r<s} n_r`.

**Formalization Note** At `L = fun _ => m` this is (10) exactly. For a general profile it is the
shape of (57), p.38, printed with exact exponents; the "`(n/S)+O(1)`" of (41) is not meant literally.
The case `B = 1` has `q = 0`, with `0 ^ 0 = 1`. -/
theorem gambler_ge_prophet_finite {S : ℕ} (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (L : Fin S → ℕ)
    (D : Measure ℝ) (hD : IsAdmissible D) (hB : 1 ≤ effHorizon γ L) (ρ : Rule)
    (hρ : acceptProb D ρ = 1 / effHorizon γ L) :
    (∑ s : Fin S, γ ^ (s : ℕ) *
        (1 - 1 / effHorizon γ L) ^ (∑ r : Fin S with r < s, L r) *
        (1 - (1 - 1 / effHorizon γ L) ^ L s)) * prophet γ L D ≤
      gambler γ L D ρ := by sorry

end EffHorizonProphet
