-- Prove2me | Theorems.Thm_BhangaleHypergraph_Main_schrijver_count
-- name    : BhangaleHypergraph.Main.schrijver_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:06:08.779867+00:00
-- url     : https://prove2.me/theorems/6e318eb2-5734-4291-b444-91116aafb4b6
-- title:
--   Lemma 2.9 — Schrijver vertex count
-- statement:
--   For $1\le h$, $2h\le m$ and $d=m-2h$, the stable-set vertex count satisfies both equalities and the bound
--   $$|V(SG(m,h))|=\frac{m}{m-h}\binom{m-h}{h}=\frac{m}{m-h}\binom{m-h}{d}\le2m^d.$$
--   In particular, $d=0$ is included. The fractions are real, not truncated integer division.
--
--   This exact count and bound control the local-core sizes.
--
--   Differences from the source:
--   - encoding: one-based finite label and color sets → zero-based Fin types and finite subsets; reason: subtracting one gives a bijection and preserves every instance
--   - encoding: integer counting identities with a displayed fraction → counts and binomial coefficients embedded in the reals; reason: m-h is positive under the stated hypotheses and no division is truncated
-- source:
--   Amey Bhangale, STOC 2027 submission #1052 (October 2026), Lemma 2.9, p. 9 (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1052.pdf

import Definitions.Def_BhangaleHypergraph_Main_Restricted

namespace BhangaleHypergraph.Main

theorem schrijver_count (m h : ℕ) (hh : 1 ≤ h) (hm : 2 * h ≤ m) :
    let d := m - 2 * h
    (Fintype.card (SchrijverVertex m h) : ℝ) =
      (m : ℝ) / (m - h : ℕ) * Nat.choose (m - h) h ∧
    (Fintype.card (SchrijverVertex m h) : ℝ) =
      (m : ℝ) / (m - h : ℕ) * Nat.choose (m - h) d ∧
    (Fintype.card (SchrijverVertex m h) : ℝ) ≤ 2 * (m : ℝ) ^ d := by sorry

end BhangaleHypergraph.Main
