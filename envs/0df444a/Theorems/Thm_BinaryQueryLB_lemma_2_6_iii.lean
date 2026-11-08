-- Prove2me | Theorems.Thm_BinaryQueryLB_lemma_2_6_iii
-- name    : BinaryQueryLB.lemma_2_6_iii
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T01:48:15.645245+00:00
-- url     : https://prove2.me/theorems/99465002-73d2-4333-b6d7-940a388964a5
-- title:
--   Lemma 2.6(iii) — $F_{W'}=F_W$ implies $W'=W$
-- statement:
--   Let $d\ge2$, $R,M>0$ and $W,W'\in\mathcal W$. If $F_{W'}=F_W$ as functions on $\mathbb R^d$, then $W'=W$.
--
--   Identifiability makes the canonical chart well defined: the subgradient $g_W$ assigned to $F_W$ does not depend on how $F_W$ is written.
--
--   Differences from the source:
--   - encoding: m = ⌊d/2⌋ → m = d / 2 (natural-number division); reason: the same number
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Lemma 2.6(iii), p.13

import Mathlib
import Definitions.Def_BinaryQueryLB_FW__386b32
import Definitions.Def_BinaryQueryLB_Wset

namespace BinaryQueryLB

/-- **Lemma 2.6(iii) (Identifiability).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Lemma 2.6(iii), p.13: "Let `W ∈ 𝒲`. … (iii) If
`W′ ∈ 𝒲` and `F_{W′} = F_W`, then `W′ = W`."

**Formalization Note.** `F_{W′} = F_W` is equality of functions ℝ^d → ℝ. -/
theorem lemma_2_6_iii (d : ℕ) (hd : 2 ≤ d) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (W W' : Fin (d / 2) → EuclideanSpace ℝ (Fin (d / 2))) (hW : W ∈ Wset (d / 2)) (hW' : W' ∈ Wset (d / 2))
    (h : FW d R M W' = FW d R M W) : W' = W := by sorry

end BinaryQueryLB
