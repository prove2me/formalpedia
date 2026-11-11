-- Prove2me | Theorems.Thm_BlottoFPTAS_Main_lemma_5_8
-- name    : BlottoFPTAS.Main.lemma_5_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:43:50.543484+00:00
-- url     : https://prove2.me/theorems/10da2544-7674-4317-ab1e-effa96dbb96c
-- title:
--   Lemma 5.8 — the arc-minimum reconstruction L(P) raises the opponent's supremum by at most Σ(v′_j)²/V + V/k ≤ 9e/40
-- statement:
--   Let $e=2^{-a}$ ($a\ge1$) and $v'_j=w'_j/Q'$ for positive integer weights $w'_j$. Suppose the reduction replaced the light battlefields ($v'_j\le e/10$) by $k=8/e$ representative battlefields. For every distribution $P$ on allocations of the reduced game that spend at most one and every opposing budget $c\ge0$,
--   $$U_{v'}(L(P);c)\le U_{v_{\mathrm{red}}}(P;c)+\frac{\sum_{j\text{ light}}(v'_j)^2}V+\frac Vk\le U_{v_{\mathrm{red}}}(P;c)+\frac{9e}{40}.$$
--   The representative bids may be dependent and need not have identical marginals. This is the cost of returning from the reduced game to the original battlefields.
--
--   Differences from the source:
--   - generalization: w′ the weights ⌈256 n v_j / e⌉ of the first rounding → any positive integer weights w′; reason: the lemma uses only v′ = w′/Q′ positive; the rounding output is a special case
--   - encoding: reduced battlefields, unordered; ess inf of Z over the arc → kept battlefields in original order, then the k representatives; least k·x_(r) over the cells meeting the arc in positive length; reason: the order does not change the game; the essential infimum of a step function is this minimum
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), p. 43, Lemma 5.8

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_Game
import Definitions.Def_BlottoFPTAS_Main_Reduction

open MeasureTheory

namespace BlottoFPTAS.Main

/-- **Lemma 5.8** (Bichler, Ghosh, arXiv:2611.05221, held version sha256 cac3638e…, p. 43).
Let `e = 2^{-a}` and let `v′_j = w′_j / Q′` come from positive integer weights. Suppose the light
battlefields (`v′_j ≤ e/10`) were replaced by `k = 8/e` representative battlefields. For every
distribution `P` on reduced allocations spending at most one and every opposing budget `c ≥ 0`,
`U_{v′}(L(P); c) ≤ U_{v_red}(P; c) + ∑_{j light} (v′_j)²/V + V/k ≤ U_{v_red}(P; c) + 9e/40`. -/
theorem lemma_5_8 {n : ℕ} (a : ℕ) (ha : 1 ≤ a) (w' : Fin n → ℕ) (hw' : ∀ j, 1 ≤ w' j)
    (hrep : Replaced a w') (P : Measure (Fin (mRed a w') → ℝ))
    (hP : IsStrategy (mRed a w') 1 P) (c : ℝ) (hc : 0 ≤ c) :
    U (vPrime w') (reconLaw a w' P) c ≤
        U (vRed a w') P c + (∑ j ∈ lightSet a w', vPrime w' j ^ 2) / Vlight a w' +
          Vlight a w' / kRep a ∧
      U (vRed a w') P c + (∑ j ∈ lightSet a w', vPrime w' j ^ 2) / Vlight a w' +
          Vlight a w' / kRep a ≤ U (vRed a w') P c + 9 * eR a / 40 := by sorry

end BlottoFPTAS.Main
