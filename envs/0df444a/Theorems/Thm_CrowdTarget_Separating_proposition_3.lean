-- Prove2me | Theorems.Thm_CrowdTarget_Separating_proposition_3
-- name    : CrowdTarget.Separating.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:04.102371+00:00
-- url     : https://prove2.me/theorems/6d02db1a-ceb1-4bcd-ada3-b39ebbc1867c
-- title:
--   Proposition 3: a separating equilibrium always exists; the H-type charges $v_H$ and sets target $C^*(\alpha)$
-- statement:
--   Consider the crowdfunding signaling game in which the creator chooses both her funding target $C$ and reward price $p$, and fix the uninformed fraction $\alpha\in[0,1]$. Let
--   $$
--   C^*(\alpha)=\begin{cases}S_H,&\alpha\le\alpha^*,\\ S_L+\sqrt{S_L^2+\bar N^2(\alpha^2v_H^2-\alpha v_HB)},&\text{otherwise},\end{cases}
--   $$
--   with $B$ from (2) and $\alpha^*$ from (3). Then:
--
--   1. the designs $(S_L,v_L)$ for the L-type and $(C^*(\alpha),v_H)$ for the H-type form a separating equilibrium that survives the intuitive criterion; in particular a separating equilibrium always exists;
--   2. in every separating equilibrium $(d_L,d_H)$ that survives the intuitive criterion, $d_L=(S_L,v_L)$, and, unless $\alpha=1$ and $S_L=S_H$, the H-type charges the full-information price and signals through the target only: $d_H=(C^*(\alpha),v_H)$.
--
--   The result says that signaling in rewards-based crowdfunding is done by raising the funding target, which makes success less likely, rather than by distorting the price.
--
--   **Formalization Note** "Any separating equilibrium" is read as any equilibrium that survives the intuitive criterion, which the paper uses to select among a continuum of equilibria (p. 11). The exception $\alpha=1$, $S_L=S_H$ is stated in the proof (Online Supplement p. 5), where $(C^*,v_H)$ is no longer the unique surviving design.
-- source:
--   Chakraborty, Swinney, Signaling to the Crowd, SSRN 2885457 (rev. June 2019), p. 15, Proposition 3, (5)

import Mathlib
import Definitions.Def_CrowdTarget_Separating_Setting

namespace CrowdTarget.Separating

/-- Chakraborty, Swinney, Signaling to the Crowd, SSRN 2885457 (rev. June 2019), p. 15, Proposition 3 (goal).

For every uninformed fraction `α ∈ [0, 1]`:
1. the designs `(S_L, v_L)` for the L-type and `(C∗(α), v_H)` for the H-type form a separating
   equilibrium that survives the intuitive criterion ("a separating equilibrium always exists");
2. in any separating equilibrium that survives the intuitive criterion, the L-type plays
   `(S_L, v_L)` and, unless `α = 1` and `S_L = S_H`, the H-type plays `(C∗(α), v_H)`.

**Formalization Note** "Any separating equilibrium" is read as any that survives the intuitive
criterion, which the paper uses to select among a continuum (p. 11). The exception
`α = 1 ∧ S_L = S_H` is the proof's own (Online Supplement p. 5: there `(C∗, v_H)` "is no longer the
unique campaign design that survives the intuitive criterion"). -/
theorem proposition_3 (P : Params) (hP : P.Standing) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    IsSepEq P α ⟨P.SL, P.vL⟩ ⟨Cstar P α, P.vH⟩ ∧
    SurvivesIC P α ⟨P.SL, P.vL⟩ ⟨Cstar P α, P.vH⟩ ∧
    ∀ dL dH : Design, IsSepEq P α dL dH → SurvivesIC P α dL dH →
      dL = ⟨P.SL, P.vL⟩ ∧
      (¬ (α = 1 ∧ P.SL = P.SH) → dH = ⟨Cstar P α, P.vH⟩) := by sorry

end CrowdTarget.Separating
