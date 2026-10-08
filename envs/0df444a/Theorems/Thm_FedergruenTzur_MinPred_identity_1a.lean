-- Prove2me | Theorems.Thm_FedergruenTzur_MinPred_identity_1a
-- name    : FedergruenTzur.MinPred.identity_1a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:36:49.401808+00:00
-- url     : https://prove2.me/theorems/613dd0bf-36bd-4e71-a3a0-da445b2c9159
-- title:
--   Identity (1a): S(i, j) = S(i, k) + S(k, j) + [D(j) − D(k)][H(k − 1) − H(i − 1)] for i < k < j
-- statement:
--   In the dynamic lot size model, let $S(i,j) = \sum_{r=i}^{j-1} h_r (D(j) - D(r))$ be the zero-inventory carrying cost of an order in period $i$ covering the demands of periods $i, \dots, j$. For periods $1 \le i < k < j$,
--   $$
--   S(i, j) = S(i, k) + S(k, j) + [D(j) - D(k)]\,[H(k-1) - H(i-1)]. \tag{1a}
--   $$
--
--   The identity splits the carrying cost of a long order interval at an intermediate period $k$: the demand of periods $k+1, \dots, j$ is carried from $i$ to $k$ at unit cost $h_i + \dots + h_{k-1} = H(k-1) - H(i-1)$. It is the tool behind the linearity of the cost differences in Lemma 2.
-- source:
--   Federgruen and Tzur, A Simple Forward Algorithm to Solve General Dynamic Lot Sizing Models with n Periods in O(n log n) or O(n) Time, Management Science 37(8), 1991, p. 912, §1, identity (1a)

import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Model

namespace FedergruenTzur.MinPred

open LotSizing

/-- Identity (1a), §1, p. 912: for `i < k < j` (periods, so `1 ≤ i`),
`S(i, j) = S(i, k) + S(k, j) + [D(j) - D(k)][H(k - 1) - H(i - 1)]`. -/
theorem identity_1a (P : LotSizing) (i k j : ℕ) (hi : 1 ≤ i) (hik : i < k) (hkj : k < j) :
    P.S i j = P.S i k + P.S k j + (P.D j - P.D k) * (P.H (k - 1) - P.H (i - 1)) := by sorry

end FedergruenTzur.MinPred
