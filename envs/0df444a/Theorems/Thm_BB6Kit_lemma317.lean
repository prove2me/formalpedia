-- Prove2me | Theorems.Thm_BB6Kit_lemma317
-- name    : BB6Kit.lemma317
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-24T08:10:35.750241+00:00
-- url     : https://prove2.me/theorems/824d045f-b9ef-428b-8004-0ac45b718e2a
-- title:
--   Kit Lemma 3.17: the points $(r+tb_1/b_3,\,s+tb_2/b_3)$ are distinct unless $b\le(R,S,T)$
-- statement:
--   **Lemma 3.17 of the Mignotte–Voutier kit.** Let $b_1,b_2,b_3$ be positive integers with $\gcd(b_1,b_2,b_3)=1$, and let $R,S,T\ge0$. The $(R+1)(S+1)(T+1)$ points $(r+tb_1/b_3,\;s+tb_2/b_3)$, $0\le r\le R$, $0\le s\le S$, $0\le t\le T$, are pairwise distinct unless $b_1\le R$, $b_2\le S$ and $b_3\le T$.
--
--   Proof: if two points coincide with $d=t-t'\ne0$, then $b_3$ divides $db_1$, $db_2$ and $db_3$, hence divides $d$. So $b_3\le|d|\le T$, and $|r-r'|=|d|b_1/b_3\ge b_1$ gives $b_1\le R$; similarly $b_2\le S$.
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, Lemma 3.17.

import Mathlib

namespace BB6Kit
theorem lemma317 (b1 b2 b3 R S T : ℕ) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hgcd : Nat.gcd (Nat.gcd b1 b2) b3 = 1) (h : ¬ (b1 ≤ R ∧ b2 ≤ S ∧ b3 ≤ T)) :
    ((Finset.range (R + 1) ×ˢ Finset.range (S + 1) ×ˢ Finset.range (T + 1)).image (fun x => ((x.1 : ℝ) + x.2.2 * ((b1 : ℝ) / b3), (x.2.1 : ℝ) + x.2.2 * ((b2 : ℝ) / b3)))).card =
      (R + 1) * (S + 1) * (T + 1) := by
  sorry
end BB6Kit
