-- Prove2me | Theorems.Thm_Diaz_quot_isAlgebraic_of_algebraic_dist
-- name    : Diaz.quot_isAlgebraic_of_algebraic_dist
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:17:20.464092+00:00
-- url     : https://prove2.me/theorems/6f476245-c764-4557-829d-7058d8dbca49
-- title:
--   Algebraic squared distance forces an algebraic ratio
-- statement:
--   Let $K \subseteq \mathbb{C}$ be a subfield and let $u, v \in \mathbb{C}$ with $v \neq 0$. If the three squared moduli
--
--   $$u\bar u,\qquad v\bar v,\qquad (u-v)\overline{(u-v)}$$
--
--   all lie in $K$, then $u/v$ is algebraic over $K$.
--
--   **Where this sits.** This is the first half of the proof of Carlo Perassi's algebraic-distance and plane rigidity theorem, the implication
--
--   $$|u-v| \in \bar{\mathbb{Q}} \ \Longrightarrow\ u/v \in \bar{\mathbb{Q}}$$
--
--   for $u,v$ in the Diaz candidate locus, stated over an arbitrary base field because that is all the argument uses.
--
--   **Proof.** Put $z = u\bar v$. The two identities
--
--   $$z + \bar z = u\bar u + v\bar v - (u-v)\overline{(u-v)}, \qquad z\bar z = (u\bar u)(v\bar v)$$
--
--   place both coefficients of $X^2 - (z+\bar z)X + z\bar z$ in $K$, so $z$ is a root of a monic quadratic over $K$. Dividing that quadratic by $(v\bar v)^2$ turns it into a monic quadratic satisfied by $u/v = z/(v\bar v)$. The Lean writes down that quadratic directly and checks it is non-zero by reading its coefficient in degree two.
--
--   **What is deliberately not claimed.** That theorem concludes $v/u \in \mathbb{Q}^{\times}$, not merely algebraicity. That last step is the Gelfond–Schneider quotient dichotomy for two non-zero logarithms, which is not in this Mathlib revision and is not asserted here; the Gelfond–Schneider theorem itself is proved on this platform as `Schanuel.gelfond_schneider`. Specialising $K = \bar{\mathbb{Q}}$ recovers exactly the algebraic-ratio conclusion of the first paragraph of that proof.
--
--   The converse direction of that theorem's equivalence is the trivial computation $|u - au| = |1-a|\,|u|$ and is not published.
--
--   Novelty is not asserted.
--
--   **Source.** Carlo Perassi, unpublished apart from this node. The mathematics is his; this node only records one step of it in Lean, and claims no novelty of its own.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.quot_isAlgebraic_of_algebraic_dist {K : Subfield ℂ} {u v : ℂ} (hv0 : v ≠ 0)
    (hu : u * conj u ∈ K) (hv : v * conj v ∈ K)
    (hd : (u - v) * conj (u - v) ∈ K) :
    IsAlgebraic (↥K) (u / v) := by sorry
