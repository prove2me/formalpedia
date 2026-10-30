-- Prove2me | Theorems.Thm_CommissionsSubscriptions_proposition_EC1_iii
-- name    : CommissionsSubscriptions.proposition_EC1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:38:03.67036+00:00
-- url     : https://prove2.me/theorems/9f7a1b72-3c98-4910-bd92-6ae1b4887091
-- title:
--   Proposition EC.1(iii) for (7) — the optimality system (EC.3) is necessary and sufficient
-- statement:
--   Consider a networked market satisfying the standing hypotheses of §2 (positive masses, $c\ge0$, every type of degree at least one, Assumption 1) and Assumption 2. For the relaxation (7):
--
--   1. for every optimal solution $(x,q^s,q^b)$ of (7), the derivatives $g'_j(q^b_j)$ and $h'_i(q^s_i)$ (one-sided limits at the end points) are finite, and there are multipliers $(\theta^b,\theta^s,\eta^b,\eta^s,\pi)$ such that the system (EC.3) holds:
--   $$g'_j(q^b_j)-\theta^b_j-\eta^b_j=0,\quad h'_i(q^s_i)-\theta^s_i+\eta^s_i=0,\quad \theta^b_j-\theta^s_i+\pi_{ij}-c_i=0\ \ ((i,j)\in E),$$
--   $$q^b_j\le b_j\perp\eta^b_j\ge0,\quad q^s_i\le s_i\perp\eta^s_i\ge0,\quad x_{ij}\ge0\perp\pi_{ij}\ge0,\quad \sum_{i:(i,j)\in E}x_{ij}=q^b_j,\quad \sum_{j:(i,j)\in E}x_{ij}=q^s_i;$$
--   2. conversely, every primal-dual pair with finite derivatives that satisfies (EC.3) is optimal in (7).
--
--   The multiplier $\theta^s$ of these conditions becomes the price vector that implements the optimum of (7) as a competitive equilibrium.
--
--   Differences from the source:
--   - encoding: seller and buyer types S = {1,…,n}, B = {1,…,m} → arbitrary finite types S, B with decidable equality; reason: a finite index set is a relabeling of {1,…,n}; the same instances
--   - encoding: inverse distributions F⁻¹ : [0,1] → [0, v̄] with v̄ ∈ ℝ₊ ∪ {∞}, and footnote 4's F⁻¹(1)·0 = 0 → Finv F u = inf{r ≥ 0 : u ≤ F r} in EReal with inf ∅ = ⊤ (Reading 1); reason: under Assumption 1 this is the paper's F⁻¹ on [0,1], with Finv F 1 = v̄ = ⊤ for unbounded support; EReal's ⊤·0 = 0 is footnote 4
--   - encoding: Assumption 1: nonatomic F on [0, v̄], extended to ℝ by 0 and 1, C¹ and strictly increasing on (0, v̄), bounded mean ∫₀^{v̄}(1 − F) < ∞ → IsValueCDF: monotone, 0 on (−∞,0], continuous, F → 1 at +∞, strictly increasing and C¹ on (0, Finv F 1), 1 − F integrable on (0,∞) (Reading 2); reason: the same class of extended CDFs; 1 − F vanishes beyond v̄, so the two integrals agree
--   - reading: Assumption 2: u F⁻¹_{b_j}(1 − u) and −u F⁻¹_{s_i}(u) strictly concave in u ∈ [0,1] → buyer function strictly concave on [0,1] (value 0 at u = 0, footnote 4); seller function strictly concave on [0,1) (Reading 3); reason: the seller function equals −v̄ = −∞ at u = 1 for unbounded support, where only the half-open reading is meaningful; for bounded support it is continuous at 1 and strict concavity on [0,1) and on [0,1] are equivalent
--   - encoding: flow vector x ∈ ℝ^{|E|} → x : S → B → ℝ, read only on E (Reading 6); reason: entries off E occur in no constraint or objective
--   - encoding: h(q^s, q^b) of (6) / objective (7a), with h_i(s_i) = ∞ for unbounded seller support → obj7 in EReal: real buyer sum minus the EReal seller sum minus the real cost sum; reason: a seller term +∞ gives −∞ as in the paper; the buyer terms are finite on [0, b_j], so no ⊤ − ⊤ arises
--   - encoding: g′_j, h′_i at the end points defined by footnote 22 as one-sided limits of the derivative; “have finite values” → HasBdryDeriv g L R q d with d : ℝ: HasDerivAt inside (L,R), Tendsto (deriv g) to d from inside at an end point (Reading 8); reason: footnote 22, with the finiteness asserted by Proposition EC.1(iii) built in
--   - encoding: (EC.3g) quantified “∀ i ∈ B” and (EC.3h) “∀ j ∈ S” → (EC.3g) for every j ∈ B, (EC.3h) for every i ∈ S; reason: index typos: the sums are over i (resp. j), so the free index is j ∈ B (resp. i ∈ S)
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), Proposition EC.1(iii), p. ec3, applied to (7) by Lemma EC.1(ii), p. ec4

import Mathlib
import Definitions.Def_CommissionsSubscriptions_MarketHyp
import Definitions.Def_CommissionsSubscriptions_Assumption2
import Definitions.Def_CommissionsSubscriptions_IsOptimal7
import Definitions.Def_CommissionsSubscriptions_KKT7

namespace CommissionsSubscriptions

/-- **Proposition EC.1(iii) for the relaxation (7) — the special KKT system (EC.3).**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), Proposition EC.1(iii), p. ec3, applied to (7) through Lemma EC.1(ii), p. ec4.

Under Assumptions 1–2 and the standing hypotheses of §2:
1. for every optimal solution `(x, q^s, q^b)` of (7), the derivatives `g′_j(q^b_j)`, `h′_i(q^s_i)`
   are finite and there is a multiplier vector `(θ^b, θ^s, η^b, η^s, π)` satisfying (EC.3);
2. ("Furthermore") every primal-dual pair for which these derivatives are finite and which
   satisfies (EC.3) is optimal in (7).

**Formalization Note.** Finiteness of the derivatives is part of `KKT7` (Reading 8). (EC.3)
contains the constraints of (7), so no separate feasibility hypothesis is needed in item 2. -/
theorem proposition_EC1_iii {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (hM : MarketHyp M) (hA2 : Assumption2 M) :
    (∀ (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ), IsOptimal7 M x qs qb →
      ∃ (θb : B → ℝ) (θs : S → ℝ) (ηb : B → ℝ) (ηs : S → ℝ) (π : S → B → ℝ),
        KKT7 M x qs qb θb θs ηb ηs π) ∧
    (∀ (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ)
        (θb : B → ℝ) (θs : S → ℝ) (ηb : B → ℝ) (ηs : S → ℝ) (π : S → B → ℝ),
        KKT7 M x qs qb θb θs ηb ηs π → IsOptimal7 M x qs qb) := by sorry

end CommissionsSubscriptions
