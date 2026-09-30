-- Prove2me | Theorems.Thm_ChanPangGQVI_ProjExistence_theorem_5_2
-- name    : ChanPangGQVI.ProjExistence.theorem_5_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:43:47.302838+00:00
-- url     : https://prove2.me/theorems/153eefa4-c43b-4a10-8c04-3530889b3d7a
-- title:
--   Theorem 5.2 — GQVI(K, f) has a solution when K maps a compact convex C into itself continuously
-- statement:
--   Let $f$ be a point-to-point mapping and $K$ a point-to-set mapping of $\mathbb R^n$ into itself. Suppose that there is a nonempty compact convex set $C\subseteq\mathbb R^n$ such that
--
--   1. $K(C)\subseteq C$, i.e. $K(x)\subseteq C$ for every $x\in C$;
--   2. $f$ is continuous on $C$;
--   3. $K$ is a nonempty, continuous, convex valued mapping on $C$: for every $x\in C$ the set $K(x)$ is nonempty, closed and convex, and $K$ is upper and lower semicontinuous at every point of $C$ with neighbourhoods relative to $C$.
--
--   Then the generalized quasi-variational inequality $\mathrm{GQVI}(K,f)$ has a solution: there is a vector $x$ with
--
--   $$
--   x\in K(x)\qquad\text{and}\qquad (x'-x)^T f(x)\ \ge\ 0\quad\text{for all } x'\in K(x).
--   $$
--
--   This is the existence theorem of the quasi-variational inequality with a moving constraint set $K(x)$ and a continuous single-valued $f$; with $K$ constant it reduces to the Hartman–Stampacchia existence theorem for variational inequalities on a compact convex set.
--
--   **Formalization Note** Upper and lower semicontinuity on $C$ are Mathlib's `UpperHemicontinuousOn K C` and `LowerHemicontinuousOn K C`. The paper takes these definitions from Berge, under which upper semicontinuous mappings have compact values, and its proof uses that $K(x)$ is closed; the closedness of $K(x)$ for $x\in C$ is therefore stated as an explicit hypothesis. Without it the statement is false ($C=[0,1]$, $K(x)\equiv(0,1)$, $f\equiv 1$). The single-valued $f$ enters the GQVI as $x\mapsto\{f(x)\}$.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 220, Theorem 5.2

import Mathlib
import Definitions.Def_ChanPangGQVI_Shared_GQVI

namespace ChanPangGQVI.ProjExistence

/-- **Theorem 5.2** (Chan and Pang 1982, p. 220). Let `f` and `K` be respectively a point-to-point
and a point-to-set mapping of `ℝⁿ` into itself. Suppose that there exists a nonempty compact
convex set `C` such that
(i) `K(C) ⊆ C`;
(ii) `f` is continuous on `C`;
(iii) `K` is a nonempty continuous convex valued mapping on `C`.
Then `GQVI(K, f)` has a solution.

"Continuous on `C`" for `K` is upper and lower semicontinuity at every point of `C` with
neighbourhoods relative to `C` (Mathlib `UpperHemicontinuousOn` / `LowerHemicontinuousOn`).

Implicit hypothesis made explicit: `K(x)` is closed for every `x ∈ C`. The paper uses Berge's
definitions, under which upper semicontinuous mappings have compact values, and its proof says
"the continuity of `K` implies that each set `K(x)` is closed". Without it the statement is false:
`C = [0, 1]`, `K(x) ≡ (0, 1)`, `f ≡ 1`. -/
theorem theorem_5_2 {n : ℕ}
    (K : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C) (hC_convex : Convex ℝ C)
    (h_i : ∀ x ∈ C, K x ⊆ C)
    (h_ii : ContinuousOn f C)
    (h_iii_nonempty : ∀ x ∈ C, (K x).Nonempty)
    (h_iii_upper : UpperHemicontinuousOn K C) (h_iii_lower : LowerHemicontinuousOn K C)
    (h_iii_convex : ∀ x ∈ C, Convex ℝ (K x))
    (hK_closed : ∀ x ∈ C, IsClosed (K x)) :
    ∃ x y, ChanPangGQVI.Shared.IsGQVISolution K (fun z => {f z}) x y := by sorry

end ChanPangGQVI.ProjExistence
