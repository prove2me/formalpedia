-- Prove2me | Theorems.Thm_EffHorizonProphet_gambler_hard_le
-- name    : EffHorizonProphet.gambler_hard_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:44:59.897104+00:00
-- url     : https://prove2.me/theorems/6ff5c1f7-8600-4dc0-afe6-782def65e2f1
-- title:
--   Eq. (14)–(15) — uniform bound on the hard instance
-- statement:
--   Let $n=\sum_sn_s\ge1$ and $0\le y<n$. For every single-quantile rule, with acceptance probability $p$ on the hard instance, the truncated tail moment satisfies
--   $$\mathbb E[Y\mathbf 1\{A\}]\le\frac1n+y\,p,$$
--   and therefore
--   $$\mathbb E[X_\tau]\le\sum_{i=1}^n\tilde\gamma^{\,s(i)-1}\Big(\frac1n+y\,p\Big)(1-p)^{i-1}.$$
--
--   The bound is uniform over rules, so it applies whatever acceptance probability the policy selects as a function of $n$ and of the instance.
--
--   Differences from the source:
--   - generalization: equal-length phases → arbitrary phase lengths $L(s)$; reason: the identity does not use equal lengths, and equal lengths are the case $L\equiv m$
--   - reading: $\tau$ is a stopping time for the filtration of $(X_i)$ (p.3), while Remarks 5 and 16 add randomized tie-breaking with coins $U_i$ → the coins are coordinates of the sample space and $\tau$ is a stopping time for $(Y_i,U_i)$; reason: Remark 16 introduces the coins this way, and the proof on p.21 uses them to reach every acceptance probability $p$
--   - encoding: acceptance is $X_i>\alpha_s$ with $\alpha_s=\tilde\gamma^{s-1}\alpha_1$ → acceptance is $Y_i>\alpha_1$, in the base scale; reason: the events coincide for $\tilde\gamma>0$; at $\tilde\gamma=0$ they differ only in phases $s\ge2$, where the reward is $0$ either way (footnote 3, p.8)
--   - encoding: phases and stages are numbered from $1$ → they are numbered from $0$; reason: a relabelling: paper phase $s$ is Lean phase $s-1$
--   - encoding: (14) is $pR_s(p)\le\tilde\gamma^{s-1}/n+\tilde\gamma^{s-1}yp$ → the tail moment bound without the common factor $\tilde\gamma^{s-1}$; reason: $pR_s(p)=\tilde\gamma^{s-1}\mathbb E[Y\mathbf 1\{A\}]$, so (14) is this bound multiplied by a nonnegative factor
--   - encoding: (15) ends with the closed geometric sum divided by $p$ → the bound is the stage sum in the second line of (15); reason: it equals the closed form for $p>0$, and has no division at $p=0$
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Eq. (14)–(15), p.21

import Mathlib
import Definitions.Def_EffHorizonProphet_gambler
import Definitions.Def_EffHorizonProphet_hardLaw
import Definitions.Def_EffHorizonProphet_acceptProb
import Definitions.Def_EffHorizonProphet_tailValue

open MeasureTheory

namespace EffHorizonProphet

/-- **Eq. (14)–(15)** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), p.21): on the hard instance, uniformly over rules with acceptance
probability `p`, the tail moment satisfies `E[Y 1{A}] ≤ 1/n + y p`, hence
`E[X_τ] ≤ ∑_i γ̃^{s(i)-1} (1/n + y p) (1-p)^{i-1}`.

**Formalization Note** (14) is printed as `p R_s(p) ≤ γ̃^{s-1}/n + γ̃^{s-1} y p`, with
`p R_s(p) = γ̃^{s-1} E[Y 1{A}]`; here the common factor is removed. The bound on `E[X_τ]` is stated
as the stage sum in the second line of (15), which avoids the printed `/p` at `p = 0`. -/
theorem gambler_hard_le {S : ℕ} (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (L : Fin S → ℕ) (y : ℝ)
    (hn : 1 ≤ ∑ s, L s) (hy0 : 0 ≤ y) (hyn : y < ((∑ s, L s : ℕ) : ℝ)) (ρ : Rule) :
    tailValue (hardLaw (∑ s, L s) y) ρ ≤
        1 / ((∑ s, L s : ℕ) : ℝ) + y * acceptProb (hardLaw (∑ s, L s) y) ρ ∧
      gambler γ L (hardLaw (∑ s, L s) y) ρ ≤
        ∑ i, γ ^ (phaseOf L i : ℕ) *
          (1 / ((∑ s, L s : ℕ) : ℝ) + y * acceptProb (hardLaw (∑ s, L s) y) ρ) *
          (1 - acceptProb (hardLaw (∑ s, L s) y) ρ) ^ (i : ℕ) := by sorry

end EffHorizonProphet
