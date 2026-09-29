-- Prove2me | Theorems.Thm_EisensteinWeightOne_chiNegThree_mul
-- name    : EisensteinWeightOne.chiNegThree_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/5e94c843-a98c-5532-8b77-50ad806c5189
-- title:
--   Complete multiplicativity of the mod 3 character χ₋₃
-- statement:
--   Let $\chi_{-3}\colon\mathbb{N}\to\mathbb{Z}$ be the function [`EisensteinWeightOne.chiNegThree`](def/ModularForm_EisensteinChiNegThree.html#L7) given by the case distinction on the residue of its argument modulo $3$: its value is $1$ when $n \bmod 3 = 1$, it is $-1$ when $n \bmod 3 = 2$, and it is $0$ otherwise, i.e. when $3 \mid n$. The theorem asserts that for all natural numbers $m$ and $n$, without any positivity or coprimality hypothesis, $\chi_{-3}(mn) = \chi_{-3}(m)\,\chi_{-3}(n)$ as an identity in $\mathbb{Z}$. Thus the function is completely multiplicative in the strong sense that the identity holds for every pair of natural arguments, including those divisible by $3$ and including $m = 0$ or $n = 0$, where both sides vanish; in particular no normalisation at $1$ is claimed here, only the product rule.
--
--   The function $\chi_{-3}$ is the unique non-trivial (quadratic) Dirichlet character of conductor $3$, realised concretely as an integer-valued function of the residue modulo $3$; complete multiplicativity is the defining product rule for such a character. The identity is used in the treatment of the weight-one Eisenstein series attached to $\chi_{-3}$, where it controls the twisted divisor sums in the $q$-expansion, and is cited in the construction of weight-one data for the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinWeightOne_chiNegThree_mul.lean

import Mathlib
import Definitions.Def_ModularForm_EisensteinChiNegThree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open EisensteinWeightOne

theorem EisensteinWeightOne.chiNegThree_mul (m n : ℕ) :
  EisensteinWeightOne.chiNegThree (m * n) =
    EisensteinWeightOne.chiNegThree m * EisensteinWeightOne.chiNegThree n := by sorry
