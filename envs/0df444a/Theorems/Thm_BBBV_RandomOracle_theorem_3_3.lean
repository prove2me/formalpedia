-- Prove2me | Theorems.Thm_BBBV_RandomOracle_theorem_3_3
-- name    : BBBV.RandomOracle.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:55:49.913992+00:00
-- url     : https://prove2.me/theorems/c0f09d44-e7fc-4107-9d89-3d41412167e4
-- title:
--   Theorem 3.3, pp. 7–8 (corrected) — changing oracle answers on pairs of total query magnitude ≤ ε²/T moves the final state by ≤ 2ε
-- statement:
--   Let $M$ be a $T$-query algorithm with workspace $W$, query strings $X$ and answers $R$, and let $A : X \to R$ be an oracle. Write $\varphi_i$ for the state of $M$ at time $i$ when every query is answered by $A$, and $q_y(\varphi_i)$ for the query magnitude of $y$ in $\varphi_i$ (Definition 3.2). Let $\varepsilon > 0$ and let $F \subseteq \{0, \dots, T-1\} \times X$ be a set of time–string pairs with
--   $$\sum_{(i,y) \in F} q_y(\varphi_i) \le \frac{\varepsilon^2}{T}.$$
--   Modify the answer to each query $(i, y) \in F$ to an arbitrary fixed value $a_{i,y} \in R$, and keep the answer $A(y)$ for $(i, y) \notin F$; the modified answers need not come from a single oracle. If $\varphi'_T$ is the final state of $M$ under the modified answers, then
--   $$\|\varphi_T - \varphi'_T\| \le 2\varepsilon .$$
--
--   This is the hybrid argument: an algorithm cannot notice a change of the oracle on queries it makes with small total amplitude. Corollary 3.4 and the lower bound of Theorem 3.5 rest on it.
--
--   **Formalization Note** The paper prints the conclusion $\le \varepsilon$, which is false. Counterexample: one query string $y$, answers in $\mathbb{Z}/2$, trivial workspace, $T = 1$, $U_0 = \mathrm{id}$, initial state $|y\rangle \otimes (|0\rangle - |1\rangle)/\sqrt 2$, $A(y) = 0$, $a_{0,y} = 1$, $F = \{(0, y)\}$, $\varepsilon = 1$: then $\sum_F q = 1 = \varepsilon^2/T$, but the two final states are $\pm$ the initial state, at distance $2$. The proof's step "the sum of squared magnitudes of all of the $E_i$ is equal to $\sum_{(i,y)\in F} q_y(|\varphi_i\rangle)$" omits a factor $4$ (the error of one step is $(O_{a} - O_A)$ applied to the querying part, of norm up to twice that part); with it the same argument gives $2\varepsilon$, which the counterexample shows is sharp. The modified answers are a time-dependent family $a_i : X \to R$ equal to $A$ off $F$. At $T = 0$ the bound $\varepsilon^2/T$ is $0$ in Lean and $F$ is empty, so the statement holds trivially there as it does on the page.
-- source:
--   Bennett, Bernstein, Brassard and Vazirani, Strengths and weaknesses of quantum computing, arXiv:quant-ph/9701001v1, pp. 7–8, Theorem 3.3 (proof p. 8); conclusion corrected from ε to 2ε

import Mathlib
import Definitions.Def_BBBV_RandomOracle_QueryModel

namespace BBBV.RandomOracle

theorem theorem_3_3 {X R W : Type} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]
    [AddCommGroup R] [Fintype W] [DecidableEq W] {T : ℕ} (M : QueryAlg X R W T)
    (A : X → R) (F : Finset (Fin T × X)) (a : Fin T → X → R)
    (ha : ∀ i y, (i, y) ∉ F → a i y = A y) (ε : ℝ) (hε : 0 < ε)
    (hF : ∑ p ∈ F, queryMag p.2 (state M (fun _ => A) p.1) ≤ ε ^ 2 / (T : ℝ)) :
    ‖final M (fun _ => A) - final M a‖ ≤ 2 * ε := by sorry

end BBBV.RandomOracle
