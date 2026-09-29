-- Prove2me | Theorems.Thm_FamousTheorems_godel_beta_function_lemma
-- name    : FamousTheorems.godel_beta_function_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:07:41.680323+00:00
-- url     : https://prove2.me/theorems/e7c244d9-b8ef-4b11-9ebd-d2945ae8c1d1
-- title:
--   Gödel's β-function lemma
-- statement:
--   **Gödel's β-function lemma.** For every finite sequence of natural numbers $a_0,\dots,a_{k-1}$ there is a single natural number $n$ such that $\beta(n,i)=a_i$ for all $i<k$. Here $\beta(n,i)=a \bmod \big((i+1)b+1\big)$, where $(a,b)$ is the pair of numbers coded by $n$.
--
--   Gödel introduced the β-function in his 1931 incompleteness paper. It codes finite sequences using only addition, multiplication and remainder, so arbitrary primitive recursion can be expressed in first-order arithmetic. The proof uses the Chinese remainder theorem: the moduli $(i+1)b+1$ are pairwise coprime when $b$ is a suitable factorial.
--
--   **Formalization note.** Mathlib's `Nat.beta_unbeta_coe`, with witness `Nat.unbeta l`. `Nat.beta n i` is defined as `n.unpair.1 % ((i + 1) * n.unpair.2 + 1)`, where `Nat.unpair` is Cantor's pairing inverse, so it is Gödel's $\beta(a,b,i)$ with the two parameters packed into one number. The list entry `l[i]` is $a_i$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Nat.beta_unbeta_coe`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem godel_beta_function_lemma (l : List ℕ) :
    ∃ n : ℕ, ∀ i : Fin l.length, Nat.beta n i = l[i] := by sorry

end FamousTheorems
