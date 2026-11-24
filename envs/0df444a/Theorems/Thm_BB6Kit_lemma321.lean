-- Prove2me | Theorems.Thm_BB6Kit_lemma321
-- name    : BB6Kit.lemma321
-- status  : Open
-- author  : @alon yuval
-- created : 2026-11-24T08:10:38.901049+00:00
-- url     : https://prove2.me/theorems/47e52565-a61c-4feb-a188-203303f70ea9
-- title:
--   Kit Lemma 3.21: projections of $\tilde\Sigma_1$ take at least $V/\mathcal M$ values unless (2.15)
-- statement:
--   **Lemma 3.21 of the Mignotte–Voutier kit** (with Lemma 3.18), in the combined form used in Section 4.
--
--   Let $R_1,S_1,T_1\ge1$, let $b_1,b_2,b_3\ge1$ be coprime, and let $\chi>0$. Put $\tilde\Sigma_1=\{(r+tb_1/b_3,\,s+tb_2/b_3)\}$ over the box $[0,R_1]\times[0,S_1]\times[0,T_1]$, and assume it has the full $V=(R_1+1)(S_1+1)(T_1+1)$ elements. Let $\mathcal M=\max\{R_1+S_1+1,\,S_1+T_1+1,\,R_1+T_1+1,\,\chi\sqrt V\}$. Assume there is no integer relation $u_1b_1+u_2b_2+u_3b_3=0$ with $\gcd(u_1,u_2,u_3)=1$ and $|u_1|\le\frac{(S_1+1)(T_1+1)}{\mathcal M-\max(S_1,T_1)}$, $|u_2|\le\frac{(R_1+1)(T_1+1)}{\mathcal M-\max(R_1,T_1)}$, $|u_3|\le\frac{(R_1+1)(S_1+1)}{\mathcal M-\max(R_1,S_1)}$; that is, condition (2.15) fails. Then for every $(\lambda,\mu)\ne(0,0)$, $$V\le\mathcal M\cdot\#\{\lambda x_1+\mu x_2:(x_1,x_2)\in\tilde\Sigma_1\}.$$
--
--   The source argues as follows. If some line $\lambda x_1+\mu x_2=c$ contained at least $\mathcal M$ points, Lemma 3.18 (lattice points of a plane in a box) would give such a relation. So every fibre has fewer than $\mathcal M$ points.
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, Lemmas 3.18 and 3.21 and their use in Section 4.

import Mathlib

namespace BB6Kit
theorem lemma321 (R1 S1 T1 b1 b2 b3 : ℕ) (χ : ℝ) (hR : 0 < R1) (hS : 0 < S1) (hT : 0 < T1)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hgcd : Nat.gcd (Nat.gcd b1 b2) b3 = 1) (hχ : 0 < χ)
    (hcard : ((Finset.range (R1 + 1) ×ˢ Finset.range (S1 + 1) ×ˢ Finset.range (T1 + 1)).image (fun x => ((x.1 : ℝ) + x.2.2 * ((b1 : ℝ) / b3), (x.2.1 : ℝ) + x.2.2 * ((b2 : ℝ) / b3)))).card =
      (R1 + 1) * (S1 + 1) * (T1 + 1))
    (h215 : ¬ (∃ u1 u2 u3 : ℤ, u1 * (b1 : ℤ) + u2 * (b2 : ℤ) + u3 * (b3 : ℤ) = 0 ∧ Int.gcd (Int.gcd u1 u2 : ℤ) u3 = 1 ∧
        (|u1| : ℝ) ≤ ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1) / ((max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) - max (S1 : ℝ) T1) ∧
        (|u2| : ℝ) ≤ ((R1 : ℝ) + 1) * ((T1 : ℝ) + 1) / ((max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) - max (R1 : ℝ) T1) ∧
        (|u3| : ℝ) ≤ ((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) / ((max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) - max (R1 : ℝ) S1))) :
    ∀ l m : ℝ, (l, m) ≠ (0, 0) →
      (((R1 + 1) * (S1 + 1) * (T1 + 1) : ℕ) : ℝ) ≤ (max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) *
        (((Finset.range (R1 + 1) ×ˢ Finset.range (S1 + 1) ×ˢ Finset.range (T1 + 1)).image (fun x => l * ((x.1 : ℝ) + x.2.2 * ((b1 : ℝ) / b3)) + m * ((x.2.1 : ℝ) + x.2.2 * ((b2 : ℝ) / b3)))).card : ℝ) := by
  sorry
end BB6Kit
