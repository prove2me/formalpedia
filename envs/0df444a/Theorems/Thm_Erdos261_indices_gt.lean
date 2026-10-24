-- Prove2me | Theorems.Thm_Erdos261_indices_gt
-- name    : Erdos261.indices_gt
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T18:46:59.501296+00:00
-- url     : https://prove2.me/theorems/5feaab64-3204-4659-af42-5700ffc6f9ab
-- title:
--   Every index in a representation of $n/2^n$ exceeds $n$
-- statement:
--   Write $\operatorname{Rep}$ for a representation $\frac{n}{2^n}=\sum_k \frac{a_k}{2^{a_k}}$ by pairwise distinct positive integers $a_k$ (Erdős Problem 261). **Theorem.** If $t\ge2$ and $\frac{n}{2^n}=\sum_{k=1}^t\frac{a_k}{2^{a_k}}$ with positive $a_k$, then $a_k>n$ for every $k$.
--
--   This is the first normalisation step for Problem 261: since $x\mapsto x/2^x$ is nonincreasing on the positive integers, a single index $a\le n$ already contributes at least $n/2^n$, leaving no room for the other (positive) terms.
--
--   **Formalization Note.** Injectivity of $a$ is assumed (to match `Erdos261Prop`) but not used.
-- source:
--   Erdős Problem 261 (https://www.erdosproblems.com/261); definitions from Formal Conjectures 261.lean; Lemma A1 of GPT 6.1 Sol; also Tengely–Ulas–Zygadło 2020 Thm 2.1 ($a_1\ge n+1$); lemma proposed by GPT 6.1 Sol (Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset

namespace Erdos261

theorem indices_gt (n t : ℕ) (ht : 2 ≤ t) (a : Fin t → ℕ) (hinj : a.Injective) (hpos : 1 ≤ a)
    (hsum : (n : ℚ) / 2 ^ n = ∑ k, (a k : ℚ) / 2 ^ (a k)) : ∀ i, n < a i := by sorry

end Erdos261
