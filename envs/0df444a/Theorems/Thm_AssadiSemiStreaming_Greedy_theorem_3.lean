-- Prove2me | Theorems.Thm_AssadiSemiStreaming_Greedy_theorem_3
-- name    : AssadiSemiStreaming.Greedy.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:42:04.228033+00:00
-- url     : https://prove2.me/theorems/42e55777-a2da-4d8f-b62f-ac2305afa61f
-- title:
--   Theorem 3 — Proper blueprints with both parameters diverging and value tending to two-thirds
-- statement:
--   Theorem 3. There is a sequence of proper blueprints (G_m)_{m⩾1} with parameters P_m, C_m → ∞ and
--   lim_{m→∞} value(G_m) = 2/3.
--
--   The sequence is indexed by natural m, with properness required for all m≥1; its unused zeroth entry is immaterial. Both integer parameters diverge, its values converge to 2/3, and the quantitative restatement holds with a single threshold and constants uniform in m.
--
--   Theorem (Restatement of Theorem 3). For any sufficiently large integer m, there exists a proper blueprint G_m with parameters P = poly(m) and C = m^O(m) such that value(G_m) = 2/3 − Θ(1/m).
--
--   Differences from the source:
--   - encoding: P=poly(m), C=m^O(m), and value=2/3−Θ(1/m) → one eventual threshold and fixed positive constants bound P by K m^d, C by m^(e m), and the value deficit between a/m and b/m; reason: these are the standard upper-growth and two-sided deficit meanings; parameters also diverge and values tend to 2/3
-- source:
--   Assadi, Jiang and Xiang (2026), Semi-Streaming Matching in a Single Pass II: Greedy is Optimal, supplied STOC 2027 submission manuscript (published basis per source.meta.json; SHA-256 8f66fdf7cb422cdd3accbae4cb24ebc61dd7ddb2e5e2d5422f4de6fc3f99395d), Theorem 3, printed p. 7 / PDF 9; Theorem (Restatement of Theorem 3), printed p. 16 / PDF 18

import Definitions.Def_AssadiSemiStreaming_Greedy_Construction
open Filter

namespace AssadiSemiStreaming.Greedy

theorem theorem_3 :
    ∃ G : ℕ → Blueprint,
      (∀ m ≥ 1, (G m).Proper) ∧
      Tendsto (fun m => (G m).P) atTop atTop ∧
      Tendsto (fun m => (G m).C) atTop atTop ∧
      Tendsto (fun m => (G m).value) atTop (nhds (2 / 3 : ℝ)) ∧
      ∃ a b K : ℝ, 0 < a ∧ 0 < b ∧ 0 < K ∧ ∃ d e N : ℕ, 1 ≤ e ∧ 1 ≤ N ∧
        ∀ m ≥ N,
          ((G m).P : ℝ) ≤ K * (m : ℝ) ^ d ∧
          (G m).C ≤ m ^ (e * m) ∧
          a / m ≤ 2 / 3 - (G m).value ∧ 2 / 3 - (G m).value ≤ b / m := by sorry

end AssadiSemiStreaming.Greedy
