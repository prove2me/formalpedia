-- Prove2me | Theorems.Thm_CommissionsSubscriptions_lemma_EC1_ii_seller
-- name    : CommissionsSubscriptions.lemma_EC1_ii_seller
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:35:33.406998+00:00
-- url     : https://prove2.me/theorems/8cd9e5e0-d68d-4f22-a02c-d1e1579a7779
-- title:
--   Lemma EC.1(ii), seller half — regularity of $h_i(q)=F^{-1}_{s_i}(q/s_i)q$
-- statement:
--   Consider a networked market satisfying the standing hypotheses of §2 (positive masses, $c\ge0$, every type of degree at least one, Assumption 1) and Assumption 2. For every seller type $i$, the function $h_i(q)=F^{-1}_{s_i}(q/s_i)\,q$ on $[0,s_i]$ satisfies:
--
--   1. $h_i$ is continuously differentiable and strictly convex on $(0,s_i)$;
--   2. $h_i$ is continuous at $q=0$ (relative to $[0,s_i]$);
--   3. whenever $h_i(s_i)<\infty$, $h_i$ is continuous at $q=s_i$ (relative to $[0,s_i]$);
--   4. $h'_i(0)=\lim_{q\downarrow0}h'_i(q)=0$;
--   5. the limit $h'_i(s_i)=\lim_{q\uparrow s_i}h'_i(q)$ exists in $[-\infty,\infty]$ and $h'_i(s_i)>-\infty$.
--
--   These are the conditions (EC.1.1-2), (EC.1.1-3) and (EC.1.1-7) on the seller terms of the framework problem (EC.1) for the relaxation (7).
--
--   Differences from the source:
--   - encoding: seller and buyer types S = {1,…,n}, B = {1,…,m} → arbitrary finite types S, B with decidable equality; reason: a finite index set is a relabeling of {1,…,n}; the same instances
--   - encoding: inverse distributions F⁻¹ : [0,1] → [0, v̄] with v̄ ∈ ℝ₊ ∪ {∞}, and footnote 4's F⁻¹(1)·0 = 0 → Finv F u = inf{r ≥ 0 : u ≤ F r} in EReal with inf ∅ = ⊤ (Reading 1); reason: under Assumption 1 this is the paper's F⁻¹ on [0,1], with Finv F 1 = v̄ = ⊤ for unbounded support; EReal's ⊤·0 = 0 is footnote 4
--   - encoding: Assumption 1: nonatomic F on [0, v̄], extended to ℝ by 0 and 1, C¹ and strictly increasing on (0, v̄), bounded mean ∫₀^{v̄}(1 − F) < ∞ → IsValueCDF: monotone, 0 on (−∞,0], continuous, F → 1 at +∞, strictly increasing and C¹ on (0, Finv F 1), 1 − F integrable on (0,∞) (Reading 2); reason: the same class of extended CDFs; 1 − F vanishes beyond v̄, so the two integrals agree
--   - reading: Assumption 2: u F⁻¹_{b_j}(1 − u) and −u F⁻¹_{s_i}(u) strictly concave in u ∈ [0,1] → buyer function strictly concave on [0,1] (value 0 at u = 0, footnote 4); seller function strictly concave on [0,1) (Reading 3); reason: the seller function equals −v̄ = −∞ at u = 1 for unbounded support, where only the half-open reading is meaningful; for bounded support it is continuous at 1 and strict concavity on [0,1) and on [0,1] are equivalent
--   - encoding: flow vector x ∈ ℝ^{|E|} → x : S → B → ℝ, read only on E (Reading 6); reason: entries off E occur in no constraint or objective
--   - encoding: h(q^s, q^b) of (6) / objective (7a), with h_i(s_i) = ∞ for unbounded seller support → obj7 in EReal: real buyer sum minus the EReal seller sum minus the real cost sum; reason: a seller term +∞ gives −∞ as in the paper; the buyer terms are finite on [0, b_j], so no ⊤ − ⊤ arises
--   - encoding: h_i(q) = F⁻¹_{s_i}(q/s_i) q : [0, s_i] → ℝ ∪ {∞} → hR: q · toReal(F⁻¹_{s_i}(q/s_i)) for derivatives and continuity; hS: the EReal value, for the condition h_i(s_i) < ∞; reason: hR equals h_i on [0, s_i), and also at s_i when h_i(s_i) < ∞; derivatives on (0, s_i) and their limits read only these values
--   - encoding: one-sided limits g′_j(0), g′_j(b_j), h′_i(s_i) of footnote 22, possibly infinite → limits of the real derivative taken in EReal; reason: g′_j(0) = ∞ and h′_i(s_i) = ∞ occur for unbounded support
--   - encoding: “continuous at q = 0” (and at b_j, s_i) for a function on [0, b_j] (resp. [0, s_i]) → ContinuousWithinAt relative to the closed interval; reason: the functions are defined on the closed interval only
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), Lemma EC.1(ii), p. ec4; (EC.1.1-2), (EC.1.1-3), (EC.1.1-7) and footnote 22, p. ec2

import Mathlib
import Definitions.Def_CommissionsSubscriptions_MarketHyp
import Definitions.Def_CommissionsSubscriptions_Assumption2
import Definitions.Def_CommissionsSubscriptions_hR
import Definitions.Def_CommissionsSubscriptions_hS

open Filter Topology

namespace CommissionsSubscriptions

/-- **Lemma EC.1(ii), seller half — (EC.1.1-2), (EC.1.1-3) and (EC.1.1-7) for `h_i`.**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), Lemma EC.1(ii), p. ec4, with Assumptions (EC.1.1-2), (EC.1.1-3), (EC.1.1-7) and
footnote 22, p. ec2.

Under Assumptions 1–2, for every seller type `i`, the function `h_i(q) = F⁻¹_{s_i}(q/s_i) q`:
1. is continuously differentiable and strictly convex on `(0, s_i)` (EC.1.1-2);
2. is continuous at `q = 0` (relative to `[0, s_i]`) (EC.1.1-2);
3. whenever `h_i(s_i) < ∞`, is continuous at `q = s_i` (relative to `[0, s_i]`) (EC.1.1-2);
4. `h′_i(0) := lim_{q↓0} h′_i(q) = 0` (EC.1.1-7, which contains `h′_i(0) ∈ [0, ∞)` of EC.1.1-3);
5. `h′_i(s_i) := lim_{q↑s_i} h′_i(q)` exists in `[−∞, ∞]` and is `> −∞` (EC.1.1-3).

**Formalization Note.** `hR` is the real-valued `h_i` (exact on `[0, s_i)`, and at `s_i` when
`h_i(s_i) < ∞`); `hS` is the `EReal`-valued `h_i`, used for the condition `h_i(s_i) < ∞`. The
limit at `s_i` is taken in `EReal`, since `h′_i(s_i) = ∞` is possible. -/
theorem lemma_EC1_ii_seller {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (hM : MarketHyp M) (hA2 : Assumption2 M) (i : S) :
    (ContDiffOn ℝ 1 (hR M i) (Set.Ioo 0 (M.s i)) ∧
      StrictConvexOn ℝ (Set.Ioo 0 (M.s i)) (hR M i)) ∧
    ContinuousWithinAt (hR M i) (Set.Icc 0 (M.s i)) 0 ∧
    (hS M i (M.s i) < ⊤ → ContinuousWithinAt (hR M i) (Set.Icc 0 (M.s i)) (M.s i)) ∧
    Tendsto (deriv (hR M i)) (𝓝[>] 0) (𝓝 0) ∧
    (∃ L : EReal, L ≠ ⊥ ∧
      Tendsto (fun q => ((deriv (hR M i) q : ℝ) : EReal)) (𝓝[<] (M.s i)) (𝓝 L)) := by sorry

end CommissionsSubscriptions
