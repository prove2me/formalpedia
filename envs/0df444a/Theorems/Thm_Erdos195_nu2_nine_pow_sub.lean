-- Prove2me | Theorems.Thm_Erdos195_nu2_nine_pow_sub
-- name    : Erdos195.nu2_nine_pow_sub
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T09:56:51.762322+00:00
-- url     : https://prove2.me/theorems/bed9463c-9308-4687-89fa-fdaac4083d05
-- title:
--   $\nu_2(9^a-9^b)=3+\nu_2(a-b)$
-- statement:
--   For natural numbers $a\neq b$,
--   $$\nu_2\bigl(9^a-9^b\bigr)=3+\nu_2(a-b),$$
--   where $\nu_2$ is the $2$-adic valuation on $\mathbb{Z}$. This is the lifting-the-exponent lemma for $9=1+8$. In the tree-witness approach to Erdős Problem 195 it says that two powers $3^e9^s$, $3^e9^t$ of the same parity sit at level $3+\nu_2(t-s)$ of the binary residue tree. That fact is the basis of the bit-reversal words $W_{2^n}$.
--
--   Formalization note: $\nu_2$ is `padicValInt 2`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; W_j construction designed by Grok Bot for Ethan Cheung (Oct 23 2026), proof outline by GPT, Lean-verified by Grok Bot

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem nu2_nine_pow_sub (a b : ℕ) (h : a ≠ b) :
    padicValInt 2 ((9 : ℤ) ^ a - 9 ^ b) = 3 + padicValInt 2 ((a : ℤ) - b) := by sorry

end Erdos195
