-- Prove2me | Theorems.Thm_BlockCycleRotation_cost_add_gcd
-- name    : BlockCycleRotation.cost_add_gcd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:52:00.104042+00:00
-- url     : https://prove2.me/theorems/f20499a8-cd6d-43d3-a890-10928e99ed01
-- title:
--   Equation (12): the move count of the block cycle algorithm
-- statement:
--   For all $n,k$, the number of moves the block cycle algorithm performs satisfies
--   $$\operatorname{cost}(n,k) + \gcd(n,k) = n + 2\,\operatorname{remSum}(n,k),$$
--   where $\operatorname{remSum}(n,k)$ is the sum of the remainders produced by the Euclidean algorithm on the pair $(n,k)$.
--
--   This is Lemma 11(2) with equation (7) of the paper: the algorithm performs $n - \gcd(n,k)$ moves of one type and $2\,\operatorname{remSum}(n,k)$ of the other. It is stated additively so that it holds unconditionally, with no truncated natural-number subtraction and no hypothesis relating $n$ and $k$; every later cost estimate is obtained by transporting a statement about $\operatorname{remSum}$ across this identity.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Observation 12. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Algorithm.lean#L117-L139

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Euclid
import Mathlib

open BlockCycleRotation

theorem BlockCycleRotation.cost_add_gcd : ∀ k n : ℕ, cost n k + Nat.gcd n k = n + 2 * remSum n k := by sorry
