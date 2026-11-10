-- Prove2me | Theorems.Thm_DNFSatMQ_Main_lemma_6_2
-- name    : DNFSatMQ.Main.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:32:15.630029+00:00
-- url     : https://prove2.me/theorems/5bafb80f-dc02-4baa-8b80-7e34165ef5d1
-- title:
--   Lemma 6.2 — first-satisfied masses: Σ 2^{−3w_i/2} √p_i ≤ 1, hence Σ √p_i ≤ 2^{3w/2}
-- statement:
--   Let $\Omega=\{0,1\}^d$ ($d\ge0$) with $\mu = U_d$. Let $c_1,\dots,c_r$ be a possibly empty ordered list of conjunctions with widths $w_1,\dots,w_r$, and
--   $$B_i = C_i\setminus\bigcup_{j<i}C_j,\qquad p_i = \mu(B_i).$$
--   Then
--   $$\sum_{i=1}^r 2^{-3w_i/2}\sqrt{p_i}\le 1, \tag{8}$$
--   and in particular, if every $w_i \le w$, then $\sum_{i=1}^r\sqrt{p_i}\le 2^{3w/2}$ (9).
--
--   Differences from the source:
--   - encoding: a term: literals on distinct variables → a partial assignment `Conj n = Fin n → Option Bool`; reason: §2 defines terms as noncontradictory; same objects
--   - encoding: coordinates [n] = {1, …, n} and bits {0, 1} → `Fin n` (coordinates 0, …, n−1) and `Bool`; reason: Lean convention; same instances
--   - generalization: w (an integer bound on the widths) → every real w with all wᵢ ≤ w; reason: contains the integer case; for real w it follows from w′ = ⌊w⌋
-- source:
--   Zelin Li, Learning DNF from Satisfying Assignments with Membership Queries, STOC 2027 submission (manuscript sha256 2e246dc4…2670), Lemma 6.2, p. 23 (PDF 24)

import Mathlib
import Definitions.Def_DNFSatMQ_Main_Basic

namespace DNFSatMQ.Main

/-- Lemma 6.2 (p. 23), inequalities (8) and (9). -/
theorem lemma_6_2 {d : ℕ} (cs : List (Conj d)) :
    (∑ i : Fin cs.length, (2 : ℝ) ^ (-(3 * ((cs.get i).width : ℝ)) / 2) *
        Real.sqrt ((((cs.get i).cube \ listUnion (cs.take i)).card : ℝ) / 2 ^ d) ≤ 1) ∧
    ∀ w : ℝ, (∀ i : Fin cs.length, ((cs.get i).width : ℝ) ≤ w) →
      ∑ i : Fin cs.length,
          Real.sqrt ((((cs.get i).cube \ listUnion (cs.take i)).card : ℝ) / 2 ^ d) ≤
        (2 : ℝ) ^ (3 * w / 2) := by sorry

end DNFSatMQ.Main
