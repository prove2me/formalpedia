-- Prove2me | Theorems.Thm_EulerMascheroni_Rivoal_hasSum_alternating_descFactorial_div_sub
-- name    : EulerMascheroni.Rivoal.hasSum_alternating_descFactorial_div_sub
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T21:20:48.172247+00:00
-- url     : https://prove2.me/theorems/9baac78d-26e3-4dab-ac78-7881a0f7933a
-- title:
--   Shifted alternating series for $\operatorname{Ein}(1)$
-- statement:
--   For every $j\ge0$,
--   $$
--   \sum_{M>j}\frac{(-1)^M\,M^{(j)}}{M!\,(M-j)}=\sum_{M>j}\frac{(-1)^M}{(M-j)!\,(M-j)}=-(-1)^j\operatorname{Ein}(1),\qquad \operatorname{Ein}(1)=\sum_{k\ge1}\frac{(-1)^{k-1}}{k\cdot k!}.
--   $$
--
--   The substitution $M=j+k$ with $k\ge1$ reduces this to the defining series of $\operatorname{Ein}(1)$. It evaluates the contribution of the simple fractions $b_jM^{(j)}/(M-j)$ in the partial-fraction decomposition behind Rivoal's forms, and so produces their $\theta=e\operatorname{Ein}(1)$ coefficient.
--
--   **Formalization Note** Stated in $\mathbb C$ with the platform function `EulerMascheroni.Mixed.ein 1`; the summand is written for all $M\ge0$, with value $0$ when $M\le j$.
-- source:
--   Elementary series lemmas for Rivoal's linear forms: T. Rivoal, Michigan Math. J. 61 (2012), Prop. 4 and Lemma 4 (at z=-1); Lemma S2 of the accompanying research notes (Q_CHILD_PROOF.md).

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Factorial.Basic
import Definitions.Def_eulerMascheroni_mixedCover

theorem EulerMascheroni.Rivoal.hasSum_alternating_descFactorial_div_sub (j : ℕ) :
    HasSum (fun M : ℕ => if j < M then
        (-1 : ℂ) ^ M * (M.descFactorial j : ℂ) / ((M.factorial : ℂ) * ((M - j : ℕ) : ℂ)) else 0)
      (-(-1) ^ j * EulerMascheroni.Mixed.ein 1) := by sorry
