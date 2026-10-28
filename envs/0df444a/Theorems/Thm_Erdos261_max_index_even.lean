-- Prove2me | Theorems.Thm_Erdos261_max_index_even
-- name    : Erdos261.max_index_even
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T18:46:51.224864+00:00
-- url     : https://prove2.me/theorems/6bc7b23f-77c3-41d5-b771-f7001dfcf73d
-- title:
--   The largest index of a representation of $n/2^n$ is even
-- statement:
--   Write $\operatorname{Rep}$ for a representation $\frac{n}{2^n}=\sum_k \frac{a_k}{2^{a_k}}$ by pairwise distinct positive integers $a_k$ (Erdős Problem 261). **Theorem.** If $t\ge2$ and $\frac{n}{2^n}=\sum_{k=1}^t\frac{a_k}{2^{a_k}}$ with distinct positive $a_k$, then $\max_k a_k$ is even.
--
--   In the carry formulation, the top column has coefficient $c_N=N$ and incoming carry $0$, so $N=2r_N$. (It is the case $a_t-a_{t-1}\ge1$ of the Tengely–Ulas–Zygadło divisibility $2^{a_t-a_{t-1}}\mid a_t$.)
--
--   **Formalization Note.** $\max$ is `Finset.univ.sup a`.
-- source:
--   Erdős Problem 261 (https://www.erdosproblems.com/261); definitions from Formal Conjectures 261.lean; remark after Theorem A3 of GPT 6.1 Sol; cf. Tengely–Ulas–Zygadło 2020 Thm 2.1; lemma proposed by GPT 6.1 Sol (Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset

namespace Erdos261

theorem max_index_even (n t : ℕ) (ht : 2 ≤ t) (a : Fin t → ℕ) (hinj : a.Injective) (hpos : 1 ≤ a)
    (hsum : (n : ℚ) / 2 ^ n = ∑ k, (a k : ℚ) / 2 ^ (a k)) : Even (Finset.univ.sup a) := by sorry

end Erdos261
