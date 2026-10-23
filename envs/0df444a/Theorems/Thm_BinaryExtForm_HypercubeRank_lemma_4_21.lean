-- Prove2me | Theorems.Thm_BinaryExtForm_HypercubeRank_lemma_4_21
-- name    : BinaryExtForm.HypercubeRank.lemma_4_21
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:29.915056+00:00
-- url     : https://prove2.me/theorems/5b900fba-9f56-42f6-9394-0742efd6c84b
-- title:
--   Lemma 4.21, p. 14 — f_{B^L}(α) is the number of trailing 1's of (α)_2, the largest t with 2^t | α + 1
-- statement:
--   Let $B^L = B^L(d)$ be the logarithmic binarization and $\alpha \in \{0, \dots, 2^d - 2\}$. Write $(\alpha)_2 \in \{0,1\}^d$ for the reverse of the base-2 expansion of $\alpha$, so that position $i$ holds the coefficient of $2^{i-1}$. Then:
--
--   1. $f_{B^L}(\alpha)$ is the largest number of $1$'s in $(\alpha)_2$ that are not preceded by any $0$, i.e. the length of the initial run of $1$'s of $(\alpha)_2$;
--   2. equivalently, $f_{B^L}(\alpha)$ is the largest $t$ such that $2^t$ divides $\alpha + 1$.
--
--   **Formalization Note.** Positions are indexed from $0$, position $m$ holding bit `α.testBit m`. Part 1 is stated as the number of positions $m < d$ such that bits $0, \dots, m$ of $\alpha$ are all $1$, which is the length of the initial run of $1$'s. Part 2 is `IsGreatest {t | 2 ^ t ∣ α + 1}`. The single level $\alpha$ is the one-element family `![α]`.
-- source:
--   Aprile, Conforti, Di Summa, Binary extended formulations and sequential convexification, arXiv:2106.00354v1, p. 14, Lemma 4.21 ((α)_2 defined on p. 12)

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model

namespace BinaryExtForm.HypercubeRank
theorem lemma_4_21 {d : ℕ} (α : ℕ) (hα : α + 2 ≤ 2 ^ d) :
    fB (BL d) ![α] = Set.ncard {m : ℕ | m < d ∧ ∀ m' ≤ m, α.testBit m' = true} ∧
    IsGreatest {t : ℕ | 2 ^ t ∣ α + 1} (fB (BL d) ![α]) := by sorry
end BinaryExtForm.HypercubeRank
