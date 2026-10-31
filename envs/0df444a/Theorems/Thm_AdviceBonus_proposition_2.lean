-- Prove2me | Theorems.Thm_AdviceBonus_proposition_2
-- name    : AdviceBonus.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:45:58.813156+00:00
-- url     : https://prove2.me/theorems/ec822c70-de03-4642-9397-52b6ebf6e108
-- title:
--   Proposition 2 — for $w<w^*_f$ the symmetric equilibrium with $f>0$, $0<b<w$ is unique, has cutoffs $(1/2,\bar q,1-\bar q)$ free of $w$, $f$ falls, $b$ rises (corrected: needs $b<w$)
-- statement:
--   Let the posterior distribution satisfy the standing assumptions and let $p,c\in\mathbb R$. Let $\bar q\in(0,1/2)$ solve
--   $$
--   \bar q=\frac12-\frac{2G(\bar q)}{g(\bar q)} \qquad(15)
--   $$
--   (the solution is unique by Lemma 3), and put
--   $$
--   f^*(w)=p-c-2wH(\bar q)\quad(16),\qquad b^*(w)=\frac{4G(\bar q)}{g(\bar q)}\,w\quad(14),\qquad w^*_f=\frac{p-c}{2H(\bar q)}\quad(18),
--   $$
--   with $H$ from (17). For every liability $w$ with $0<w<w^*_f$:
--
--   1. **Uniqueness.** Every symmetric equilibrium compensation scheme $(f,b)$ with $f>0$ and $0<b<w$ (so that the advice to the second customer is informative) equals $(f^*(w),b^*(w))$.
--   2. **Existence.** If each firm's profit satisfies first-order sufficiency when the rival offers $(f^*(w),b^*(w))$ (every own scheme in the interior of the strategy set with interior advice cutoffs at which both own partial derivatives vanish is a best response), then $(f^*(w),b^*(w))$ is a symmetric equilibrium compensation scheme.
--   3. **Cutoffs.** $f^*(w)>0$ and $b^*(w)>0$, and at the scheme $(f^*(w),b^*(w))$ the advice cutoffs are
--   $$
--   (\bar q_1,\bar q^A_2,\bar q^B_2)=\big(\tfrac12,\ \bar q,\ 1-\bar q\big),
--   $$
--   which do not depend on $w$.
--
--   Moreover, $w\mapsto f^*(w)$ is strictly decreasing and $w\mapsto b^*(w)$ is strictly increasing on $(0,w^*_f)$.
--
--   This is the paper's answer to its title: raising the advisor's liability below $w^*_f$ leaves the bias of advice ($\bar q<1/2$) exactly where it was, because firms shift pay from commission to bonus.
--
--   Differences from the source:
--   - reading: "there is a unique symmetric equilibrium compensation scheme" → unique among symmetric equilibria with f > 0 and 0 < b < w; reason: p.16 "the optimal compensation for a symmetric equilibrium, with f > 0 and b > 0. As we show below, such an equilibrium is unique", and p.19 "our characterization … when f_n > 0 and b_n > 0"
--   - correction: uniqueness among symmetric equilibria with f > 0 and b > 0 → uniqueness among symmetric equilibria with f > 0 and 0 < b < w (informative advice to the second customer); b*(w) = (1 − 2q̄)w < w lies in this class; reason: the printed claim is false: for g ≡ 1, p − c = 1, w = 1/5 the scheme (f, b) = (3/5, 3/5) is a symmetric equilibrium (q̄A2 = 0, q̄B2 = 1; in the lock-in region firm A's profit is (1/2 + (T − 9/5)/(2/5))(2 − T) in T = 2f′ + b′, maximal at T = 9/5 with value 1/10, and a fine grid over X finds no better deviation for either firm), with w = 1/5 < w*_f = 51/44, and it differs from (f*, b*) = (1 − 44/255, 2/15)
--   - reading: existence, resting on the assumed strict quasiconcavity of profits (pp.36–37) → existence under first-order sufficiency against the candidate scheme: for each firm, every own scheme in the interior of X with interior cutoffs at which both own partial derivatives vanish maximizes its profit over X when the rival offers (f*(w), b*(w)); on the existence clause only; reason: the proofs use the assumption only to pass from first-order conditions to optimality; literal strict quasiconcavity fails for every G (profit is affine where firm A wins both sales), and without the interior-cutoff restriction the condition fails whenever p − c > w (profit is identically 0 where the firm never sells)
--   - reading: "a symmetric equilibrium" → a symmetric pure Nash equilibrium of the compensation stage at the given price p, strategy set {f ≥ 0, 2f + b ≥ 0}, profits (6); reason: §4 takes p_n = p as given (p.16), and p.8 gives the limited-liability strategy set
--   - reading: q̄1 by (4), no corner convention → clamped to [0, 1]; reason: the convention of footnote 19 for (2) and (3); at the equilibrium all cutoffs are interior
--   - reading: density g > 0 on [0, 1], hazard rate increasing on [0, 1] → g continuous and positive on [0, 1], hazard rate weakly increasing on [0, 1); reason: the proofs use continuity (intermediate value theorem, p.35) and the hazard rate is undefined at q = 1
--   - reading: "the commission f decreases with the size of w while the bonus b increases" → w ↦ f*(w) StrictAntiOn and w ↦ b*(w) StrictMonoOn (0, w*_f); reason: the comparative statics of the equilibrium formulas (16), (14)
--   - encoding: "unique advice cutoffs …, which are all independent of w" → the cutoffs at the equilibrium are (1/2, q̄, 1 − q̄) with q̄ any solution of (15) in (0, 1/2); reason: (15) does not involve w and its solution is unique (Lemma 3)
--   - generalization: the model's standing assumption (1) on v_h, v_l and c → not assumed; p and c arbitrary reals; reason: §4 takes p as given and (1) only restricts the customer side; the statement specializes to the source's under (1), and for p ≤ c the range 0 < w < w*_f is empty
--   - encoding: advisor payoffs include w_l → w_l dropped; reason: it cancels from every cutoff
-- source:
--   Honda–Inderst–Ottaviani, When Liability is Not Enough, SSRN 4125013 (May 2022), Proposition 2, p.19, with eqs. (14), p.17, (15), p.17, (16)–(17), p.18, (18), p.19

import Mathlib
import Definitions.Def_AdviceBonus_Model
import Definitions.Def_AdviceBonus_Equilibrium
import Definitions.Def_AdviceBonus_ClosedForms

namespace AdviceBonus

/-- **Proposition 2**, p.19 (Honda–Inderst–Ottaviani, SSRN 4125013, May 2022). Let `q̄ ∈ (0, 1/2)`
solve (15), `q̄ = 1/2 − 2G(q̄)/g(q̄)` (unique by Lemma 3), and put
`f*(w) = p − c − 2w H(q̄)` (16), `b*(w) = 4G(q̄)/g(q̄) · w` (14) and `w*_f = (p − c)/(2H(q̄))` (18).
For every liability `0 < w < w*_f`:
1. (uniqueness) every symmetric equilibrium scheme `(f, b)` with `f > 0` and `0 < b < w`
   (informative advice to the second customer) is `(f*(w), b*(w))`;
2. (existence) if each firm's profit satisfies first-order sufficiency against the rival scheme
   `(f*(w), b*(w))`, then `(f*(w), b*(w))` is a symmetric equilibrium;
3. `f*(w) > 0`, `b*(w) > 0`, and at `(f*(w), b*(w))` the advice cutoffs are
   `(q̄_1, q̄^A_2, q̄^B_2) = (1/2, q̄, 1 − q̄)`, independent of `w`.
Moreover the commission `f*` is strictly decreasing and the bonus `b*` strictly increasing in `w`
on `(0, w*_f)`.

**Formalization Note** (corrected) `b < w` in clause 1 is not printed. Without it clause 1 is false:
for `g ≡ 1` (`q̄ = 1/6`, `H(q̄) = 22/51`, `w*_f = 51/44`), `p − c = 1` and `w = 1/5`, the scheme
`(3/5, 3/5)` is a symmetric equilibrium with `f, b > 0` (both second cutoffs clamp; no deviation in
`X` beats the profit `1/10`), and it differs from `(f*, b*) = (1 − 44/255, 2/15)`. Note
`b*(w) = (1 − 2q̄) w < w`, so `(f*, b*)` lies in the class of clause 1. -/
theorem proposition_2 (D : Dist) (p c qbar : ℝ) (hq : qbar ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hfix : qbar = 1 / 2 - 2 * D.G qbar / D.g qbar) :
    (∀ w : ℝ, 0 < w → w < wStar D p c qbar →
      (∀ s : ℝ × ℝ, IsSymEq D p c w s → 0 < s.1 → 0 < s.2 → s.2 < w →
        s = (p - c - 2 * w * H D qbar, 4 * D.G qbar / D.g qbar * w)) ∧
      (FOCSufficient D p c w (p - c - 2 * w * H D qbar, 4 * D.G qbar / D.g qbar * w) →
        IsSymEq D p c w (p - c - 2 * w * H D qbar, 4 * D.G qbar / D.g qbar * w)) ∧
      0 < p - c - 2 * w * H D qbar ∧ 0 < 4 * D.G qbar / D.g qbar * w ∧
      q1 D w (p - c - 2 * w * H D qbar, 4 * D.G qbar / D.g qbar * w)
          (p - c - 2 * w * H D qbar, 4 * D.G qbar / D.g qbar * w) = 1 / 2 ∧
      q2A w (p - c - 2 * w * H D qbar, 4 * D.G qbar / D.g qbar * w)
          (p - c - 2 * w * H D qbar, 4 * D.G qbar / D.g qbar * w) = qbar ∧
      q2B w (p - c - 2 * w * H D qbar, 4 * D.G qbar / D.g qbar * w)
          (p - c - 2 * w * H D qbar, 4 * D.G qbar / D.g qbar * w) = 1 - qbar) ∧
    StrictAntiOn (fun w => p - c - 2 * w * H D qbar) (Set.Ioo 0 (wStar D p c qbar)) ∧
    StrictMonoOn (fun w => 4 * D.G qbar / D.g qbar * w) (Set.Ioo 0 (wStar D p c qbar)) := by sorry

end AdviceBonus
