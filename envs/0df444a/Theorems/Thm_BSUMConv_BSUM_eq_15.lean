-- Prove2me | Theorems.Thm_BSUMConv_BSUM_eq_15
-- name    : BSUMConv.BSUM.eq_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:26:05.19722+00:00
-- url     : https://prove2.me/theorems/9131622f-c8f4-48fb-9a60-482ad20279cc
-- title:
--   (15), p. 11 — at a limit point z of the BSUM iterates, lim f(xʳ) = f(z)
-- statement:
--   In the setting of Theorem 2 (closed convex blocks $\mathcal X_i$, $f$ continuous on $\mathcal X$, Assumption 2, BSUM iterates $x^r$ under the cyclic rule), let $z$ be a limit point of the sequence $(x^r)$. Then
--
--   $$\lim_{r\to\infty} f(x^r)=f(z).$$
--
--   Together with (14) this identifies the limit of the objective values, which the rest of the proof of Theorem 2(a) uses repeatedly.
--
--   **Formalization Note** "Limit point" is `MapClusterPt z atTop x`.
-- source:
--   Razaviyayn, Hong & Luo, arXiv:1209.2385v1, p. 11, proof of Theorem 2(a), display (15)

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting
import Definitions.Def_BSUMConv_BSUM_Setting

namespace BSUMConv.BSUM

open TsengBCD.Stationary Filter Topology

/-- (15), p. 11: if `z` is a limit point of a cyclic BSUM run, then
`lim_{r→∞} f(x^r) = f(z)`. -/
theorem eq_15 {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (hXconv : ∀ i, Convex ℝ (Xs i)) (hXclosed : ∀ i, IsClosed (Xs i))
    (f : X n → ℝ) (hf : ContinuousOn f (Xset Xs))
    (u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ) (hA2 : Assumption2 Xs f u)
    (s : ℕ → Fin N) (hs : IsCyclic s) (x : ℕ → X n) (hx : IsBSUMRun Xs u s x)
    (z : X n) (hz : MapClusterPt z atTop x) :
    Tendsto (fun r => f (x r)) atTop (𝓝 (f z)) := by sorry

end BSUMConv.BSUM
