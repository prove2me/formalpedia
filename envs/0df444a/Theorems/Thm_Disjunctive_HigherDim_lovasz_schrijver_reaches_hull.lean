-- Prove2me | Theorems.Thm_Disjunctive_HigherDim_lovasz_schrijver_reaches_hull
-- name    : Disjunctive.HigherDim.lovasz_schrijver_reaches_hull
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:40:50.074082+00:00
-- url     : https://prove2.me/theorems/2d5c6635-d004-4495-89aa-2c8c6d7abe06
-- title:
--   Theorem 7.5 — iterating N reaches the integer hull
-- statement:
--   This is Theorem 7.5 of Balas's *Disjunctive Programming*, cited to Lovász and
--   Schrijver [99]: iterating the $N$-operator $p$ times reaches the mixed 0-1 program's integer
--   hull.
--
--   $$
--   N^p(K) = \mathrm{conv}(K_0), \qquad N^1(K) := N(K),\ N^t(K) := N(N^{t-1}(K))\ (t \ge 2).
--   $$
--
--   The book's proof: "Corollary 7.3 implies Theorem 7.5. Again, this follows from $N(K) \subseteq
--   P_j(K)$, $j=1,\dots,p$" — the same one-step containment underlying Theorem 7.4, applied at every
--   iteration, sandwiches the iterated lift between $K_0$ and its convex hull.
--
--   **Formalization Note.** The iteration is formalized via a dependent family of representations
--   `A t, b t` for `t : Fin (p+1)` together with a hypothesis `hStep` asserting that step `t.succ`'s
--   polyhedron equals `NOp` applied to step `t`'s — the same pattern `04-normal-forms`'s Theorem 4.10
--   uses for a varying ambient representation across an iteration, needed here because each
--   successive $N^t(K)$ genuinely has a different, larger constraint system (not a fixed matrix
--   raised to a power).
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 94, Theorem 7.5

import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic
import Definitions.Def_Disjunctive_HigherDim_Lifts

namespace Disjunctive.HigherDim

/-- Theorem 7.5 (Balas §7.2, p. 93, [99]): iterating the Lovász-Schrijver operator `p` times
(over a sequence of representations `(A_t, b_t)`, each defining the previous step's `N`-image)
reaches the convex hull of `K₀`. `p := Nprime.card`. -/
theorem lovasz_schrijver_reaches_hull {n p : ℕ} {mA : Fin (p + 1) → ℕ}
    (A : (t : Fin (p + 1)) → Matrix (Fin (mA t)) (Fin n) ℝ)
    (b : (t : Fin (p + 1)) → Fin (mA t) → ℝ) (Nprime : Finset (Fin n)) (hp : Nprime.card = p)
    (hStep : ∀ t : Fin p, Poly (A t.succ) (b t.succ) = NOp (A t.castSucc) (b t.castSucc) Nprime) :
    Poly (A (Fin.last p)) (b (Fin.last p)) = convexHull ℝ (K0Set (A 0) (b 0) Nprime) := by sorry

end Disjunctive.HigherDim
