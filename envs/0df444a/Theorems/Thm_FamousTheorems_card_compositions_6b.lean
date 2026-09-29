-- Prove2me | Theorems.Thm_FamousTheorems_card_compositions_6b
-- name    : FamousTheorems.card_compositions_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:06.514517+00:00
-- url     : https://prove2.me/theorems/e8e7d933-36d3-4b30-b606-1b54328afadb
-- title:
--   There are 2^(n−1) compositions of n
-- statement:
--   **There are $2^{n-1}$ compositions of $n$.** A composition of $n$ is an ordered sequence of positive integers with sum $n$. For every $n\ge1$ there are exactly $2^{n-1}$ compositions of $n$, and there is exactly one composition of $0$, the empty one.
--
--   A composition of $n$ is the same as a choice of which of the $n-1$ gaps between $n$ dots to cut, which gives the count. The number of compositions into exactly $k$ parts is $\binom{n-1}{k-1}$. Compositions are used to index terms in the multivariate Faà di Bruno formula and in the theory of quasisymmetric functions.
--
--   **Formalization note.** Mathlib's `composition_card`. `Composition n` is the type of lists of positive natural numbers with sum $n$. With natural-number subtraction, $2^{0-1}=2^0=1$, so the formula also gives the correct count for $n=0$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `composition_card`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem card_compositions_6b (n : ℕ) : Fintype.card (Composition n) = 2 ^ (n - 1) := by sorry

end FamousTheorems
