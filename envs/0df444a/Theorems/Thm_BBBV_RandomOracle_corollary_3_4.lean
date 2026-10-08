-- Prove2me | Theorems.Thm_BBBV_RandomOracle_corollary_3_4
-- name    : BBBV.RandomOracle.corollary_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:56:43.07825+00:00
-- url     : https://prove2.me/theorems/012f8191-f06b-4a96-985f-ce21afead959
-- title:
--   Corollary 3.4, p. 8 (corrected) — all but 4T²/ε² strings y can be changed in the oracle while moving the final state by ≤ ε
-- statement:
--   Let $M$ be a $T$-query algorithm and $A : X \to R$ an oracle; write $\varphi_T$ for the final state of $M$ with oracle $A$, and for $y \in X$ and any oracle $A_y$ that agrees with $A$ on every $x \ne y$, write $\varphi_T^{(y)}$ for the final state with oracle $A_y$. Then for every $\varepsilon > 0$ there is a set $S \subseteq X$ with
--   $$|S| \le \frac{4T^2}{\varepsilon^2}$$
--   such that $\|\varphi_T - \varphi_T^{(y)}\| \le \varepsilon$ for every $y \notin S$ and every such $A_y$.
--
--   The set $S$ depends only on $M$, $A$ and $\varepsilon$, not on $y$ or on the new answer at $y$. The corollary says that a $T$-query algorithm is sensitive to the oracle's value at only $O(T^2)$ strings, which is what makes a search over $2^n$ strings need $\Omega(2^{n/2})$ queries.
--
--   **Formalization Note** The paper prints the cardinality bound $2T^2/\varepsilon^2$, which is false. Counterexample: $16$ query strings, an algorithm with $T = 1$ querying the uniform superposition of all strings with answer register $(|0\rangle - |1\rangle)/\sqrt 2$ in one answer bit, $A \equiv 0$, and $A_y$ flipping that bit at $y$; then $\|\varphi_T - \varphi_T^{(y)}\| = 2/\sqrt{16} = 0.5$ for every $y$, so with $\varepsilon = 0.45$ every $y$ must lie in $S$, while $2T^2/\varepsilon^2 < 10 < 16$. The bound printed follows from the uncorrected Theorem 3.3; with the corrected Theorem 3.3 (bound $2\varepsilon$) the proof's threshold becomes $\varepsilon^2/(4T)$ and the count $4T^2/\varepsilon^2$.
-- source:
--   Bennett, Bernstein, Brassard and Vazirani, Strengths and weaknesses of quantum computing, arXiv:quant-ph/9701001v1, p. 8, Corollary 3.4 (and its proof); cardinality bound corrected from 2T²/ε² to 4T²/ε²

import Mathlib
import Definitions.Def_BBBV_RandomOracle_QueryModel

namespace BBBV.RandomOracle

theorem corollary_3_4 {X R W : Type} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]
    [AddCommGroup R] [Fintype W] [DecidableEq W] {T : ℕ} (M : QueryAlg X R W T)
    (A : X → R) (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset X, (S.card : ℝ) ≤ 4 * (T : ℝ) ^ 2 / ε ^ 2 ∧
      ∀ y ∉ S, ∀ Ay : X → R, (∀ x, x ≠ y → Ay x = A x) →
        ‖final M (fun _ => A) - final M (fun _ => Ay)‖ ≤ ε := by sorry

end BBBV.RandomOracle
