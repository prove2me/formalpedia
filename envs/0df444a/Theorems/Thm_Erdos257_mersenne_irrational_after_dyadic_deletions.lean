-- Prove2me | Theorems.Thm_Erdos257_mersenne_irrational_after_dyadic_deletions
-- name    : Erdos257.mersenne_irrational_after_dyadic_deletions
-- status  : Proved
-- author  : @Mceppaglia
-- created : 2026-11-20T17:10:30.649625+00:00
-- url     : https://prove2.me/theorems/a00a61a4-3823-4af2-8ce9-d05b106c038f
-- title:
--   Irrationality after deleting arbitrary power-of-two exponents from the Erdős–Borwein series
-- statement:
--   Start with all positive integer exponents. Let $D$ be any subset of the powers of two, including $1=2^0$. Then the convergent real series $\sum_{n\ge1,\ n\notin D}(2^n-1)^{-1}$ is irrational. The set $D$ may be empty, finite, or infinite.
-- source:
--   Restricted case of Erdős problem 257 (https://openproofnetwork.org/problems/erdos-257/). Exact statement: “Irrationality after deleting arbitrary power-of-two exponents,” private research note, 20 November 2026, Theorem 1. Matt directed the investigation with OpenAI Codex assistance. P. Erdős, “On arithmetical properties of Lambert series,” J. Indian Math. Soc. 12 (1948), pp. 63–66, proves the full-series case. The proof uses Will Cook’s bounded first-block frame in Erdos249257/CertificateKernel.lean, lines 7886–8023 of commit 5411c40344eeb0371a5f34eafc9b22f6b4499017.

import Mathlib

theorem Erdos257.mersenne_irrational_after_dyadic_deletions
    (D : Set ℕ) (hD : D ⊆ Set.range (fun j : ℕ => (2 : ℕ) ^ j)) :
    Irrational (∑' n : {n : ℕ // 0 < n ∧ n ∉ D}, 1 / ((2 : ℝ) ^ n.val - 1)) := by sorry
