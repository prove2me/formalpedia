-- Prove2me | Theorems.Thm_EffHorizonProphet_prophet_hard_tendsto
-- name    : EffHorizonProphet.prophet_hard_tendsto
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:44:13.870119+00:00
-- url     : https://prove2.me/theorems/dbed1794-9938-4380-b59e-1ba844332abb
-- title:
--   Eq. (13) — prophet value on the hard instance, via (12)
-- statement:
--   Fix $S\ge1$, $0\le\tilde\gamma\le1$ and a common value $y\ge0$. On the hard instance ($Y=n$ with probability $1/n^2$, $Y=y$ otherwise),
--   $$\mathbb E\Big[\max_{i\in[n]}X_i\Big]=y+c_{\tilde\gamma}+o(1)\qquad(n\to\infty).$$
--
--   The rare value contributes $c_{\tilde\gamma}$ because the earliest rare draw has the largest discount, and the first phase always carries the common value $y$.
--
--   Differences from the source:
--   - generalization: phases of equal length $n/S$ with $S\mid n$ and $n\to\infty$ → any sequence of profiles $L_t$ with $n_t=\sum_s L_t(s)\to\infty$ and $L_t(s)/n_t\to 1/S$; reason: this is the reading "(or asymptotically $n_s/n\to 1/S$)" of p.3 and contains the printed case $L_t\equiv t$, for which a sanity lemma checks the hypotheses
--   - encoding: $y+c_{\tilde\gamma}+o(1)$ → a limit of the sequence along $t$; reason: the same statement
--   - encoding: the exact formula (12) as an intermediate display → only the limit (13) is stated; reason: (12) is a step of the proof of (13) and needs no separate clause
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Eq. (12)–(13), p.20

import Mathlib
import Definitions.Def_EffHorizonProphet_IsEqualProfile
import Definitions.Def_EffHorizonProphet_prophet
import Definitions.Def_EffHorizonProphet_hardLaw
import Definitions.Def_EffHorizonProphet_cGamma

open Filter Topology

namespace EffHorizonProphet

/-- **Eq. (12)–(13)** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), p.20): on the hard instance with a fixed common value `y ≥ 0`, the
prophet value is `E[max_i X_i] = y + c_γ̃ + o(1)`, for every `0 ≤ γ̃ ≤ 1`. -/
theorem prophet_hard_tendsto {S : ℕ} (hS : 1 ≤ S) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    {L : ℕ → Fin S → ℕ} (hL : IsEqualProfile L) {y : ℝ} (hy : 0 ≤ y) :
    Tendsto (fun t => prophet γ (L t) (hardLaw (∑ s, L t s) y)) atTop (𝓝 (y + cGamma S γ)) := by sorry

end EffHorizonProphet
