-- Prove2me | Theorems.Thm_EffHorizonProphet_limit_ratio_hard
-- name    : EffHorizonProphet.limit_ratio_hard
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:44:01.746655+00:00
-- url     : https://prove2.me/theorems/3fc3c4b4-188d-4f79-b57a-ca0d8509e0c5
-- title:
--   Eq. (16) and boundary regimes — limit of the bound on the hard instance
-- statement:
--   Fix $S\ge1$, $\tilde\gamma\in[0,1]$, $y\ge0$, and any upper bound $C$ of $f_S(\cdot,y)$ on $(0,\infty)$. Let $p_n\in[0,1]$ be arbitrary. Then for each $u>C$, eventually
--   $$\sum_{i=1}^n\tilde\gamma^{\,s(i)-1}\Big(\frac1n+y\,p_n\Big)(1-p_n)^{i-1}<u\;\mathbb E\Big[\max_{i\in[n]}X_i\Big],$$
--   the expectation being on the hard instance with common value $y$.
--
--   This covers all behaviours of $x_n=np_n$ at once: the regimes $x_n\to0$, $x_n\to x\in(0,\infty)$ and $x_n\to\infty$ treated separately in the paper.
--
--   Differences from the source:
--   - generalization: phases of equal length $n/S$ with $S\mid n$ and $n\to\infty$ → any sequence of profiles $L_t$ with $n_t=\sum_s L_t(s)\to\infty$ and $L_t(s)/n_t\to 1/S$; reason: this is the reading "(or asymptotically $n_s/n\to 1/S$)" of p.3 and contains the printed case $L_t\equiv t$, for which a sanity lemma checks the hypotheses
--   - encoding: phases and stages are numbered from $1$ → they are numbered from $0$; reason: a relabelling: paper phase $s$ is Lean phase $s-1$
--   - generalization: $p_n$ is the acceptance probability of a policy → $p_n$ is an arbitrary sequence in $[0,1]$; reason: every such sequence is attained by rules with coins on the hard instance for $n\ge2$, and the argument uses only $p_n\in[0,1]$
--   - encoding: $\limsup\mathrm{CR}_n(\tau_n)\le\sup_{u>0}f_S(u,y)$, along subsequences of $x_n$ → an eventual inequality for each $u>C$, with $C$ any upper bound of $f_S(\cdot,y)$, applied to the bound (15) and multiplied through by the prophet value; reason: the same content: no subsequence appears, and the sup is replaced by any upper bound, which gives the statement at $C=\sup f_S(\cdot,y)$
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Eq. (16), pp.21–22; p.26

import Mathlib
import Definitions.Def_EffHorizonProphet_IsEqualProfile
import Definitions.Def_EffHorizonProphet_fS
import Definitions.Def_EffHorizonProphet_hardLaw
import Definitions.Def_EffHorizonProphet_prophet

open Filter

namespace EffHorizonProphet

/-- **Eq. (16) and the boundary regimes** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), pp.21–22 and p.26): for a fixed `y ≥ 0` and any
per-stage acceptance probabilities `p_n`, the bound (15) divided by the prophet value has limsup at
most `sup_{x>0} f_S(x, y)`, in every subsequential regime of `x_n = n p_n`: `x_n → 0`,
`x_n → x ∈ (0, ∞)` and `x_n → ∞`.

**Formalization Note** `C` is any upper bound of `f_S(·, y)` on `(0, ∞)`, and "limsup ≤ C" is stated
in the form `∀ u > C, ∀ᶠ t, …`, multiplied through by the prophet value. No subsequence appears. -/
theorem limit_ratio_hard {S : ℕ} (hS : 1 ≤ S) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    {L : ℕ → Fin S → ℕ} (hL : IsEqualProfile L) {y : ℝ} (hy : 0 ≤ y) {C : ℝ}
    (hC : ∀ x, 0 < x → fS S γ x y ≤ C) (p : ℕ → ℝ) (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1)
    {u : ℝ} (hu : C < u) :
    ∀ᶠ t in atTop,
      ∑ i, γ ^ (phaseOf (L t) i : ℕ) * (1 / ((∑ s, L t s : ℕ) : ℝ) + y * p t) *
          (1 - p t) ^ (i : ℕ) <
        u * prophet γ (L t) (hardLaw (∑ s, L t s) y) := by sorry

end EffHorizonProphet
