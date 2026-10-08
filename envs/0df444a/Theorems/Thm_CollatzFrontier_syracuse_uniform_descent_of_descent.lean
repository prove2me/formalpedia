-- Prove2me | Theorems.Thm_CollatzFrontier_syracuse_uniform_descent_of_descent
-- name    : CollatzFrontier.syracuse_uniform_descent_of_descent
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-04T17:25:00.42385+00:00
-- url     : https://prove2.me/theorems/7e2abde1-c1a6-4d11-b023-05fa24e4fd06
-- title:
--   Residue-class Syracuse descent with a sharp one-bit budget and no parity hypothesis on the target
-- statement:
--   Let $T$ be the Syracuse map, $T(n) = (3n+1)/2^{v_2(3n+1)}$. Fix an odd representative $m'$ and record the exponents stripped along its first $t$ steps, $a_0,\dots,a_{t-1}$, so that
--
--   $$2^{a_i}\,T^{i+1}(m') = 3\,T^{i}(m') + 1 \qquad (i<t).$$
--
--   Write $S=\sum_{i<t} a_i$ for the total number of halvings. Suppose the halvings fit inside the modulus, $S \le K$, and the representative descends, $T^t(m') < m'$. Then **every** $m \ge m'$ congruent to $m'$ modulo $2^K$ satisfies $T^t(m) < m$, using the same number of steps — with no parity hypothesis imposed on $m$ itself.
--
--   **Relation to the accepted platform theorem.** This strengthens [`syracuse_uniform_descent`](https://prove2.me/theorems/cd79de19-4613-42b0-afc9-48de75023e4a) (Terras uniformity, by shivm), whose hypotheses additionally include $m$ odd, an explicit contraction $3^t < 2^S$, and the stronger budget $S+1 \le K$. No contraction hypothesis and no parity hypothesis on $m$ are needed.
--
--   **Boundary example.** At $m'=5$, $K=4$, $t=1$, $a_0=4$, the sum $S=4$ equals $K$: the relaxed budget $S\le K$ holds, while the accepted theorem's budget $S+1\le K$, i.e. $5\le 4$, fails. The remaining hypotheses hold ($T(5)=1<5$), so this statement gives $T(5+16q)<5+16q$ for every natural $q$ directly from this witness, without separately supplying a contraction certificate.
--
--   **Sharpness.** The budget $S\le K$ cannot be relaxed any further, not even by one bit. At $m'=9$, $a_0=2$, $K=1$: $2^2\,T(9) = 3\cdot 9+1=28$ and $T(9)=7<9$, so every hypothesis holds except the budget, since $S=2=K+1$. Lifting to $m=11\equiv 9 \pmod 2$ satisfies $m'\le m$, yet $T(11)=17>11$: the conclusion fails. So $S\le K$ is exactly the boundary of validity, not merely a convenient sufficient bound.
--
--   **Formalization note.** As in the accepted theorem, the exponent sequence is supplied as a function $a:\mathbb N\to\mathbb N$ together with the hypothesis that it is the sequence of exponents $m'$'s own orbit strips; this keeps the statement free of auxiliary definitions.
-- source:
--   collatz-frontier (private repo), commit 4d656b9c9c5815305bd391f206c9d3e9587dd395, lean/CollatzFrontier/AffineDrift.lean, declaration syracuse_uniform_descent_of_descent, with the unused hypothesis `hm : Odd m` dropped (the repo's own lean/CollatzFrontier/UniformDescent.lean, declaration syracuse_uniform_descent_terminal, documents this with an explicit `clear hm`). Strengthens the accepted platform theorem syracuse_uniform_descent, https://prove2.me/theorems/cd79de19-4613-42b0-afc9-48de75023e4a (by shivm), whose underlying source is R. Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241-252.

import Definitions.Def_syracuseStep
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith

namespace CollatzFrontier

theorem syracuse_uniform_descent_of_descent (a : ℕ → ℕ) (m m' K t : ℕ)
    (hm' : Odd m')
    (hcong : m ≡ m' [MOD 2 ^ K])
    (hstep : ∀ i < t, 2 ^ (a i) * (syracuseStep^[i + 1] m') = 3 * (syracuseStep^[i] m') + 1)
    (hbudget : (∑ i ∈ Finset.range t, a i) ≤ K)
    (hdesc : syracuseStep^[t] m' < m')
    (hle : m' ≤ m) :
    syracuseStep^[t] m < m := by sorry

end CollatzFrontier
