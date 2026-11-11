-- Prove2me | Theorems.Thm_EntAssistOneWay_Separation_theorem_5_1
-- name    : EntAssistOneWay.Separation.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:15.663193+00:00
-- url     : https://prove2.me/theorems/a868251c-0dc9-4ec7-a935-529746dc7fc5
-- title:
--   Theorem 5.1 — reduction from shifted equality
-- statement:
--   For any finite group $G$ and integer $r\ge1$, set $S=\mathbb F_2^r$ and $k=2^{r+1}$. There exists a finite group $\widetilde G$ and input maps $X:G^S\times G^S\to\mathcal H_{\widetilde G,k}$ and $Y:G^S\times S\to\widetilde G$ such that
--   $$|\widetilde G|=k|G|^k,\qquad\operatorname{ShiftEq}_{G,r}(a,b)=\operatorname{Memb}_{\widetilde G,k}(X(a),Y(b))\quad\text{for every }a,b.$$
--   The equality covers both yes- and no-instances. This exact reduction transfers subgroup-membership upper bounds to the total shifted equality problem.
--
--   Differences from the source: none.
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 24, Theorem 5.1; pp. 25–26, construction

import Definitions.Def_EntAssistOneWay_Separation_GroupProblems

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- Theorem 5.1, p. 24: both directions are expressed by Boolean equality. -/
theorem theorem_5_1 (G : Type) [Group G] [Fintype G] (r : ℕ) (hr : 1 ≤ r) :
    ∃ (H : Type) (gH : Group H) (fH : Fintype H),
      letI := gH
      letI := fH
      Fintype.card H = 2 ^ (r + 1) * Fintype.card G ^ (2 ^ (r + 1)) ∧
      ∃ (X : ShiftAlice G r → SmallSubgroup H (2 ^ (r + 1)))
        (Y : ShiftBob G r → H),
        ∀ a b, shiftEq r a b = membership H (2 ^ (r + 1)) (X a) (Y b) := by sorry

end

end EntAssistOneWay.Separation
