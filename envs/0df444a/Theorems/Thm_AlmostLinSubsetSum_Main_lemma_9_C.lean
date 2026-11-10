-- Prove2me | Theorems.Thm_AlmostLinSubsetSum_Main_lemma_9_C
-- name    : AlmostLinSubsetSum.Main.lemma_9_C
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:29:00.398516+00:00
-- url     : https://prove2.me/theorems/874c9e1d-36d5-43d8-84c8-835c643b332a
-- title:
--   Lemma 9.C — greedy growth (Conlon–Fox–Pham): if $|kU|\ge2|S|$ then some $u\in U$ has $|(S+u)\setminus S|\ge|S|/(2k)$
-- statement:
--   **Lemma 9.C** (p. 43; Conlon–Fox–Pham, Lemma 2.41). Let $S,U\subset\mathbb Z^r$ be finite nonempty sets and let $k\ge1$ be an integer. If $|kU|\ge2|S|$, then some $u\in U$ satisfies
--   $$|(S+u)\setminus S|\ge\frac{|S|}{2k}.$$
--   Here $kU$ is the $k$-fold sumset and the inequality is between real numbers.
--
--   Differences from the source: none.
-- source:
--   Chen, Mao, Zhang (2026), An Almost-Linear Time Algorithm for Multidimensional Subset Sum, STOC 2027 submission, SHA-256 0cd42ca048cfff088013ad06450a278a6df72a29004c48c5c138f3f6df85d1e0, Lemma 9.C, p. 43

import Mathlib
import Definitions.Def_AlmostLinSubsetSum_Main_Basic

set_option autoImplicit false

namespace AlmostLinSubsetSum.Main

/-- **Lemma 9.C** (Greedy growth; Conlon–Fox–Pham, cited in Chen, Mao, Zhang 2026, p. 43).
Let `S, U ⊂ ℤ^r` be finite nonempty sets and let `k ≥ 1` be an integer. If `|kU| ≥ 2|S|`
(`kU` the `k`-fold sumset), then some `u ∈ U` satisfies `|(S + u) \ S| ≥ |S| / (2k)`. -/
theorem lemma_9_C {r : ℕ} (S U : Set (Fin r → ℤ)) (hSfin : S.Finite) (hUfin : U.Finite)
    (hSne : S.Nonempty) (hUne : U.Nonempty) (k : ℕ) (hk : 1 ≤ k)
    (hgrow : 2 * S.ncard ≤ (kFold k U).ncard) :
    ∃ u ∈ U, (S.ncard : ℝ) / (2 * k) ≤ (((fun x => x + u) '' S) \ S).ncard := by sorry

end AlmostLinSubsetSum.Main
