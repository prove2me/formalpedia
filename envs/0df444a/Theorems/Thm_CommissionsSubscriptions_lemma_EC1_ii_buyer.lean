-- Prove2me | Theorems.Thm_CommissionsSubscriptions_lemma_EC1_ii_buyer
-- name    : CommissionsSubscriptions.lemma_EC1_ii_buyer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:34:49.902974+00:00
-- url     : https://prove2.me/theorems/d44ec8a5-4088-491b-8dbf-35ca866d3b4b
-- title:
--   Lemma EC.1(ii), buyer half — regularity of $g_j(q)=F^{-1}_{b_j}(1-q/b_j)q$
-- statement:
--   Consider a networked market satisfying the standing hypotheses of §2 (positive masses, $c\ge0$, every type of degree at least one, Assumption 1) and Assumption 2. For every buyer type $j$, the function $g_j(q)=F^{-1}_{b_j}(1-q/b_j)\,q$ on $[0,b_j]$ satisfies:
--
--   1. $g_j$ is continuously differentiable and strictly concave on $(0,b_j)$;
--   2. $g_j$ is continuous at $q=0$ and at $q=b_j$ (relative to $[0,b_j]$); note $g_j(b_j)=0$;
--   3. the limit $g'_j(0)=\lim_{q\downarrow0}g'_j(q)$ exists in $[-\infty,\infty]$ and $g'_j(0)>0$;
--   4. the limit $g'_j(b_j)=\lim_{q\uparrow b_j}g'_j(q)$ exists in $[-\infty,\infty]$ and $g'_j(b_j)\le0$.
--
--   These are the conditions (EC.1.1-1), (EC.1.1-3) and (EC.1.1-8) on the buyer terms of the framework problem (EC.1) for the relaxation (7); they make the optimality conditions (EC.3) available.
--
--   Differences from the source:
--   - encoding: seller and buyer types S = {1,…,n}, B = {1,…,m} → arbitrary finite types S, B with decidable equality; reason: a finite index set is a relabeling of {1,…,n}; the same instances
--   - encoding: inverse distributions F⁻¹ : [0,1] → [0, v̄] with v̄ ∈ ℝ₊ ∪ {∞}, and footnote 4's F⁻¹(1)·0 = 0 → Finv F u = inf{r ≥ 0 : u ≤ F r} in EReal with inf ∅ = ⊤ (Reading 1); reason: under Assumption 1 this is the paper's F⁻¹ on [0,1], with Finv F 1 = v̄ = ⊤ for unbounded support; EReal's ⊤·0 = 0 is footnote 4
--   - encoding: Assumption 1: nonatomic F on [0, v̄], extended to ℝ by 0 and 1, C¹ and strictly increasing on (0, v̄), bounded mean ∫₀^{v̄}(1 − F) < ∞ → IsValueCDF: monotone, 0 on (−∞,0], continuous, F → 1 at +∞, strictly increasing and C¹ on (0, Finv F 1), 1 − F integrable on (0,∞) (Reading 2); reason: the same class of extended CDFs; 1 − F vanishes beyond v̄, so the two integrals agree
--   - reading: Assumption 2: u F⁻¹_{b_j}(1 − u) and −u F⁻¹_{s_i}(u) strictly concave in u ∈ [0,1] → buyer function strictly concave on [0,1] (value 0 at u = 0, footnote 4); seller function strictly concave on [0,1) (Reading 3); reason: the seller function equals −v̄ = −∞ at u = 1 for unbounded support, where only the half-open reading is meaningful; for bounded support it is continuous at 1 and strict concavity on [0,1) and on [0,1] are equivalent
--   - encoding: flow vector x ∈ ℝ^{|E|} → x : S → B → ℝ, read only on E (Reading 6); reason: entries off E occur in no constraint or objective
--   - encoding: h(q^s, q^b) of (6) / objective (7a), with h_i(s_i) = ∞ for unbounded seller support → obj7 in EReal: real buyer sum minus the EReal seller sum minus the real cost sum; reason: a seller term +∞ gives −∞ as in the paper; the buyer terms are finite on [0, b_j], so no ⊤ − ⊤ arises
--   - encoding: one-sided limits g′_j(0), g′_j(b_j), h′_i(s_i) of footnote 22, possibly infinite → limits of the real derivative taken in EReal; reason: g′_j(0) = ∞ and h′_i(s_i) = ∞ occur for unbounded support
--   - encoding: “continuous at q = 0” (and at b_j, s_i) for a function on [0, b_j] (resp. [0, s_i]) → ContinuousWithinAt relative to the closed interval; reason: the functions are defined on the closed interval only
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), Lemma EC.1(ii), p. ec4; (EC.1.1-1), (EC.1.1-3), (EC.1.1-8) and footnote 22, p. ec2

import Mathlib
import Definitions.Def_CommissionsSubscriptions_MarketHyp
import Definitions.Def_CommissionsSubscriptions_Assumption2
import Definitions.Def_CommissionsSubscriptions_gB

open Filter Topology

namespace CommissionsSubscriptions

/-- **Lemma EC.1(ii), buyer half — (EC.1.1-1), (EC.1.1-3) and (EC.1.1-8) for `g_j`.**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), Lemma EC.1(ii), p. ec4, with Assumptions (EC.1.1-1), (EC.1.1-3), (EC.1.1-8) and
footnote 22, p. ec2.

Under Assumptions 1–2, for every buyer type `j`, the function `g_j(q) = F⁻¹_{b_j}(1 − q/b_j) q`:
1. is continuously differentiable and strictly concave on `(0, b_j)` (EC.1.1-1);
2. is continuous at `q = 0` and at `q = b_j` (relative to `[0, b_j]`); here
   `g_j(b_j) = F⁻¹(0) b_j = 0 > −∞`, so the "whenever `g_j(b_j) > −∞`" clause applies (EC.1.1-1);
3. `g′_j(0) := lim_{q↓0} g′_j(q)` exists in `[−∞, ∞]` and is `> 0` (EC.1.1-8, which contains
   `g′_j(0) > −∞` of EC.1.1-3);
4. `g′_j(b_j) := lim_{q↑b_j} g′_j(q)` exists in `[−∞, ∞]` and is `≤ 0` (EC.1.1-3).

**Formalization Note.** The one-sided limits of footnote 22 are taken in `EReal`, since
`g′_j(0) = ∞` is possible (unbounded support). -/
theorem lemma_EC1_ii_buyer {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (hM : MarketHyp M) (hA2 : Assumption2 M) (j : B) :
    (ContDiffOn ℝ 1 (gB M j) (Set.Ioo 0 (M.b j)) ∧
      StrictConcaveOn ℝ (Set.Ioo 0 (M.b j)) (gB M j)) ∧
    (ContinuousWithinAt (gB M j) (Set.Icc 0 (M.b j)) 0 ∧
      ContinuousWithinAt (gB M j) (Set.Icc 0 (M.b j)) (M.b j)) ∧
    (∃ L : EReal, 0 < L ∧
      Tendsto (fun q => ((deriv (gB M j) q : ℝ) : EReal)) (𝓝[>] 0) (𝓝 L)) ∧
    (∃ L : EReal, L ≤ 0 ∧
      Tendsto (fun q => ((deriv (gB M j) q : ℝ) : EReal)) (𝓝[<] (M.b j)) (𝓝 L)) := by sorry

end CommissionsSubscriptions
