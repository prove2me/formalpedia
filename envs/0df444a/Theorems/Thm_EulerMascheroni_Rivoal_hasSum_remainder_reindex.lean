-- Prove2me | Theorems.Thm_EulerMascheroni_Rivoal_hasSum_remainder_reindex
-- name    : EulerMascheroni.Rivoal.hasSum_remainder_reindex
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T21:20:30.907837+00:00
-- url     : https://prove2.me/theorems/822a2b99-8c97-4393-80ee-a26f24bec942
-- title:
--   Partial-fraction reindexing of the remainder $S_n$
-- statement:
--   For every $n\ge0$, put $F(M)=\dfrac{\prod_{i=n+1}^{3n}(M-i)}{\prod_{i=0}^{n}(M-i)}$. Then
--   $$
--   \sum_{M\ge n+1}\frac{(-1)^M F(M)}{M!}=(-1)^{n+1}S_n,\qquad S_n=\sum_{m\ge0}\frac{(-1)^m}{m!}\left(\frac{(m+2n)!}{(m+3n+1)!}\right)^2 .
--   $$
--
--   The numerator vanishes for $n+1\le M\le 3n$. For $M=m+3n+1$ one has $F(M)/M!=\big((m+2n)!/(m+3n+1)!\big)^2/m!$. This rewrites the remainder $S_n$ of Rivoal's forms (definition `eulerMascheroni_rivoalForms`) as a series in the rational function $F$, which is then expanded in partial fractions.
--
--   **Formalization Note** The sum is stated as a `HasSum` in $\mathbb R$ over all $M\ge0$, with value $0$ when $M\le n$.
-- source:
--   Elementary series lemmas for Rivoal's linear forms: T. Rivoal, Michigan Math. J. 61 (2012), Prop. 4 and Lemma 4 (at z=-1); Lemma F1, Step 1 of the accompanying research notes (Q_CHILD_PROOF.md).

import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_eulerMascheroni_rivoalForms

theorem EulerMascheroni.Rivoal.hasSum_remainder_reindex (n : ℕ) :
    HasSum (fun M : ℕ => if n + 1 ≤ M then
        (-1 : ℝ) ^ M * ((∏ i ∈ Finset.Ico (n + 1) (3 * n + 1), ((M : ℝ) - i)) /
          (∏ i ∈ Finset.range (n + 1), ((M : ℝ) - i))) / (M.factorial : ℝ) else 0)
      ((-1) ^ (n + 1) * EulerMascheroni.Rivoal.remainder n) := by sorry
