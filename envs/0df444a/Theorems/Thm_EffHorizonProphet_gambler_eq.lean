-- Prove2me | Theorems.Thm_EffHorizonProphet_gambler_eq
-- name    : EffHorizonProphet.gambler_eq
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:45:05.570967+00:00
-- url     : https://prove2.me/theorems/ae45bdaf-9dea-4f8c-b992-21f314a55a97
-- title:
--   Eq. (7) — reward of a single-quantile rule
-- statement:
--   Let $D$ be an admissible law and $0\le\tilde\gamma\le1$. For a single-quantile rule with acceptance event $A$ and acceptance probability $p$, independence gives
--   $$\mathbb E[X_\tau]=\mathbb E[Y\mathbf 1\{A\}]\sum_{i=1}^n\tilde\gamma^{\,s(i)-1}(1-p)^{i-1},$$
--   where $s(i)$ is the phase of stage $i$.
--
--   Both halves of the characterization start from this identity: the upper bound on the hard instance and the lower bound through the truncated tail moment.
--
--   Differences from the source:
--   - generalization: the rule with $p=a/n$, equal phases → any rule, any phase lengths; reason: (7) and the first line of (15) are this identity for particular rules; independence is all it uses
--   - reading: $\tau$ is a stopping time for the filtration of $(X_i)$ (p.3), while Remarks 5 and 16 add randomized tie-breaking with coins $U_i$ → the coins are coordinates of the sample space and $\tau$ is a stopping time for $(Y_i,U_i)$; reason: Remark 16 introduces the coins this way, and the proof on p.21 uses them to reach every acceptance probability $p$
--   - encoding: acceptance is $X_i>\alpha_s$ with $\alpha_s=\tilde\gamma^{s-1}\alpha_1$ → acceptance is $Y_i>\alpha_1$, in the base scale; reason: the events coincide for $\tilde\gamma>0$; at $\tilde\gamma=0$ they differ only in phases $s\ge2$, where the reward is $0$ either way (footnote 3, p.8)
--   - encoding: phases and stages are numbered from $1$ → they are numbered from $0$; reason: a relabelling: paper phase $s$ is Lean phase $s-1$
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Eq. (7), p.9; first line of (15), p.21

import Mathlib
import Definitions.Def_EffHorizonProphet_IsAdmissible
import Definitions.Def_EffHorizonProphet_gambler
import Definitions.Def_EffHorizonProphet_acceptProb
import Definitions.Def_EffHorizonProphet_tailValue

open MeasureTheory

namespace EffHorizonProphet

/-- **Eq. (7)** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), p.9): by independence, the expected reward of a single-quantile rule is
`E[X_τ] = E[Y 1{A}] ∑_i γ̃^{s(i)-1} (1-p)^{i-1}`.

**Formalization Note** Stated for every rule and every admissible law, which is also the first line
of (15), p.21. Stages are `0`-based. -/
theorem gambler_eq {S : ℕ} (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (L : Fin S → ℕ) (D : Measure ℝ)
    (hD : IsAdmissible D) (ρ : Rule) :
    gambler γ L D ρ =
      tailValue D ρ * ∑ i, γ ^ (phaseOf L i : ℕ) * (1 - acceptProb D ρ) ^ (i : ℕ) := by sorry

end EffHorizonProphet
