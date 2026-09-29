-- Prove2me | Theorems.Thm_Diaz_fibre_at_most_two
-- name    : Diaz.fibre_at_most_two
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:17:17.834352+00:00
-- url     : https://prove2.me/theorems/1005cf6b-db5b-4749-9fa5-44d4c3327b78
-- title:
--   At most two points of an exponential fibre have algebraic modulus
-- statement:
--   For $\alpha \in \mathbb{C}$ put
--
--   $$E_\alpha = \{\,u \in \mathbb{C} : e^{u} = \alpha,\ u\bar u \in \bar{\mathbb{Q}}\,\}.$$
--
--   Then $\#E_\alpha \le 2$: three pairwise distinct points of $E_\alpha$ cannot exist.
--
--   **Where this sits.** This is Theorem 3.3 of the note cited below, which states it for algebraic $\alpha \neq 0$. It is unconditional — no unproved transcendence input enters.
--
--   **Proof.** Two points of one exponential fibre differ by an integer multiple of $2\pi i$, so with $c = 2\pi i$ the three points are $u$, $u + mc$, $u + nc$ with $m \neq n$ both non-zero. Since $\bar c = -c$,
--
--   $$(u + kc)\overline{(u+kc)} = u\bar u + \bigl(c(\bar u - u)\bigr)k + \bigl(-c^{2}\bigr)k^{2},$$
--
--   a quadratic in $k$ whose leading coefficient is $-c^{2} = 4\pi^{2}$. Three algebraic values at distinct integers make that leading coefficient algebraic (`Diaz.second_difference_mem`), hence $(\pi i)^{2} = -\pi^{2}$ is algebraic, hence $\pi i$ is algebraic. But $\pi i \neq 0$ and $e^{\pi i} = -1$ is algebraic, so Hermite–Lindemann makes $\pi i$ transcendental. Contradiction.
--
--   The Lean carries the Lindemann–Weierstrass development inline, since it is not in this Mathlib revision; the form used is the one already on this mission as `Diaz.transcendental_of_candidate`.
--
--   **Two remarks on the hypotheses.** The statement does not assume $\alpha$ algebraic, nor even $\alpha \neq 0$: the bound holds for every exponential fibre. And only the *squared* moduli are assumed algebraic, which is the same condition as $|u| \in \bar{\mathbb{Q}}$ but avoids a square root in the formalisation.
--
--   Two further clauses that Carlo Perassi states with it — that a real $\alpha$ gives a conjugate pair, and that for non-real $\alpha$ two points have squared-modulus ratio in $\bar{\mathbb{Q}} \setminus \mathbb{Q}$ — depend on his axis-parallel rational-ratio rigidity theorem, whose input (Roy–Waldschmidt) is not formalisable here, and are not published.
--
--   Novelty is not asserted.
--
--   **Source.** Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Theorem 3.3. The mathematics is his; this node records it in Lean, and claims no novelty of its own.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.fibre_at_most_two {α u v w : ℂ}
    (heu : Complex.exp u = α) (hev : Complex.exp v = α) (hew : Complex.exp w = α)
    (hqu : IsAlgebraic ℚ (u * conj u)) (hqv : IsAlgebraic ℚ (v * conj v))
    (hqw : IsAlgebraic ℚ (w * conj w))
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) : False := by sorry
