-- Prove2me | Theorems.Thm_EulerMascheroni_Rivoal_hasSum_alternating_descFactorial
-- name    : EulerMascheroni.Rivoal.hasSum_alternating_descFactorial
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T21:20:26.310195+00:00
-- url     : https://prove2.me/theorems/93a97e36-3478-4a18-b3f1-b687dd19c10d
-- title:
--   Alternating exponential series with a falling factorial
-- statement:
--   For every $j\ge0$, with the falling factorial $M^{(j)}=M(M-1)\cdots(M-j+1)$,
--   $$
--   \sum_{M\ge0}\frac{(-1)^M\,M^{(j)}}{M!}=(-1)^j e^{-1}.
--   $$
--
--   Since $M^{(j)}/M!=1/(M-j)!$ for $M\ge j$ and $M^{(j)}=0$ for $M<j$, the substitution $M=j+k$ reduces this to $\sum_k(-1)^k/k!=e^{-1}$. In the elementary proof that $1,e,e\operatorname{Ein}(1)$ are $\mathbb Q$-linearly independent it evaluates $\sum_M(-1)^MP(M)/M!$ for an integer polynomial $P$ written in the falling-factorial basis.
--
--   **Formalization Note** The falling factorial is `Nat.descFactorial M j`, and the sum is stated as a `HasSum` in $\mathbb R$.
-- source:
--   Elementary series lemmas for Rivoal's linear forms: T. Rivoal, Michigan Math. J. 61 (2012), Prop. 4 and Lemma 4 (at z=-1); Lemma S1 of the accompanying research notes (Q_CHILD_PROOF.md).

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Factorial.Basic

theorem EulerMascheroni.Rivoal.hasSum_alternating_descFactorial (j : ℕ) :
    HasSum (fun M : ℕ => (-1 : ℝ) ^ M * (M.descFactorial j : ℝ) / (M.factorial : ℝ))
      ((-1) ^ j * Real.exp (-1)) := by sorry
