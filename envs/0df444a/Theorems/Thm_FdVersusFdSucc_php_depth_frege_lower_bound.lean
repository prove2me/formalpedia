-- Prove2me | Theorems.Thm_FdVersusFdSucc_php_depth_frege_lower_bound
-- name    : FdVersusFdSucc.php_depth_frege_lower_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T10:13:53.347662+00:00
-- url     : https://prove2.me/theorems/f4e03dde-333a-4eba-9e4b-93bd8efa040d
-- title:
--   Exponential lower bound for bounded-depth Frege proofs of $\mathrm{PHP}^{n+1}_n$
-- statement:
--   Fix a depth $d\ge 0$. There is $\varepsilon=\varepsilon(d)>0$ such that for all sufficiently large $n$, every $F_d$-proof $\pi$ of the pigeonhole principle $\mathrm{PHP}^{n+1}_n$ satisfies
--   $$|\pi| \ \ge\ 2^{\,n^{\varepsilon}}.$$
--
--   This is the classical exponential lower bound for bounded-depth Frege systems, the prototype of the switching-lemma lower bounds on which separations between $F_d$ and $F_{d+1}$ rest.
-- source:
--   J. Krajíček, P. Pudlák, A. Woods, An exponential lower bound to the size of bounded depth Frege proofs of the pigeonhole principle, Random Structures & Algorithms 7(1), 1995; T. Pitassi, P. Beame, R. Impagliazzo, Exponential lower bounds for the pigeonhole principle, Computational Complexity 3, 1993. Context: Open Problem Garden, 'F_d versus F_{d+1}' (J. Krajíček), http://www.openproblemgarden.org/op/f_d_versus_f_d_1

import Definitions.Def_FdVersusFdSucc_defs

open Filter

namespace FdVersusFdSucc

/-- (Krajíček–Pudlák–Woods 1995; Pitassi–Beame–Impagliazzo 1993.) For every fixed depth `d`,
`F_d`-proofs of the pigeonhole principle `PHP^{n+1}_n` require size `2^(n^ε)` for some
`ε = ε(d) > 0` and all sufficiently large `n`. -/
theorem php_depth_frege_lower_bound (d : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n in atTop, ∀ π : List Sequent, IsDepthProofOf d π (php n) →
      (2 : ℝ) ^ ((n : ℝ) ^ ε) ≤ (proofSize π : ℝ) := by sorry

end FdVersusFdSucc
