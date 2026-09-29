-- Prove2me | Theorems.Thm_FamousTheorems_schnirelmann_lemma_7a
-- name    : FamousTheorems.schnirelmann_lemma_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:57.019985+00:00
-- url     : https://prove2.me/theorems/85fd56c5-4036-4861-8c53-7eb9a4ef19d4
-- title:
--   Schnirelmann's lemma: σ(A)+σ(B) ≥ 1 implies A+B = ℕ
-- statement:
--   **Schnirelmann's lemma.** Let $A,B\subseteq\mathbb N$ with $0\in A$ and $0\in B$, and let $\sigma$ denote Schnirelmann density, $\sigma(A)=\inf_{n\ge1}|A\cap\{1,\dots,n\}|/n$. If $\sigma(A)+\sigma(B)\ge1$, then $A+B=\mathbb N$.
--
--   Schnirelmann introduced this density in 1930 and used it to prove that every integer greater than $1$ is a sum of a bounded number of primes. This was the first result towards Goldbach's conjecture. The lemma shows that a set of positive density is an additive basis of finite order. It follows from a pigeonhole argument, and it is refined by Mann's theorem $\sigma(A+B)\ge\min(1,\sigma(A)+\sigma(B))$.
--
--   **Formalization note.** Mathlib's `add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity`. `schnirelmannDensity A` is the infimum above. `A + B` is the pointwise sumset $\{a+b:a\in A,b\in B\}$. The decidability instances are only needed to compute the finite counts.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open Pointwise

theorem schnirelmann_lemma_7a {A B : Set ℕ} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] (hA : 0 ∈ A) (hB : 0 ∈ B)
    (h : 1 ≤ schnirelmannDensity A + schnirelmannDensity B) : A + B = Set.univ := by sorry

end FamousTheorems
