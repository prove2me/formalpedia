-- Prove2me | Theorems.Thm_ChaChaTree_DynOpt_lemma_14
-- name    : ChaChaTree.DynOpt.lemma_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:22:44.334317+00:00
-- url     : https://prove2.me/theorems/5bc74488-f976-4999-86a1-c6a14fc89358
-- title:
--   Lemma 14 — a guarded right extension of any strictly independent family from a point p
-- statement:
--   Let $P$ be an instance, $p = (x,y) \in P$, and $y_{\mathrm{guard}} > y$, $x_{\mathrm{guard}} < x$ coordinates such that
--   1. either $p_{\mathrm{guard}} := (x_{\mathrm{guard}}, y_{\mathrm{guard}}) \in P$ or $y_{\mathrm{guard}} = \infty$;
--   2. the area $(x_{\mathrm{guard}}, x] \times (y, y_{\mathrm{guard}})$ contains no point of $P$;
--   3. the area $(x, \infty) \times (y, y_{\mathrm{guard}})$ contains at least one point of $P$.
--
--   Then for any set $R$ of strictly independent rectangles on $P$ there is a set $R' \supseteq R$ of strictly independent rectangles on $P$ containing a rectangle from $p$ to some point of $P$ in $(x,\infty) \times (y, y_{\mathrm{guard}})$.
--
--   Differences from the source:
--   - encoding: a rectangle □_{p,q} → the ordered pair (p, q) : Rect with IsRectOn P (p, q); reason: a rectangle is determined by its two defining points with p.y < q.y; same objects
--   - encoding: coordinates x_guard < x and y_guard > y, with y_guard = ∞ allowed → xguard : ℤ and yguard : WithTop ℕ (∞ = ⊤); reason: keys and times are integers: a finite y_guard is the time of p_guard ∈ P by condition 1, and a non-integer x_guard (possible only when y_guard = ∞) gives the same three conditions and conclusion as its floor
-- source:
--   Čech, Haeupler, Roeyskoe, Rozhoň, Tarjan, Yingchareonthawornchai, Dynamic Optimality to within O(log log log n), STOC 2027 submission (manuscript, sha256 9316fbfd…7b9e), Lemma 14, p. 16 (PDF 17)

import Mathlib
import Definitions.Def_ChaChaTree_DynOpt_Instance
import Definitions.Def_ChaChaTree_DynOpt_Rectangles

set_option autoImplicit false

namespace ChaChaTree.DynOpt

/-- **Lemma 14** (p. 16). Let `p = (x, y) ∈ P` and let `y_guard > y` (possibly `∞`) and
`x_guard < x` be coordinates such that (1) `(x_guard, y_guard) ∈ P` or `y_guard = ∞`; (2) the
area `(x_guard, x] × (y, y_guard)` contains no point of `P`; (3) the area `(x, ∞) × (y, y_guard)`
contains a point of `P`. Then every strictly independent set `R` on `P` extends to a strictly
independent `R' ⊇ R` on `P` containing a rectangle from `p` to some point of `P` in
`(x, ∞) × (y, y_guard)`. -/
theorem lemma_14 (N T : ℕ) (P : Finset (ℕ × ℕ)) (hP : IsInstance N T P) (p : ℕ × ℕ)
    (hp : p ∈ P) (xguard : ℤ) (yguard : WithTop ℕ) (hy : (p.2 : WithTop ℕ) < yguard)
    (hx : xguard < (p.1 : ℤ))
    (h1 : (∃ g ∈ P, (g.1 : ℤ) = xguard ∧ (g.2 : WithTop ℕ) = yguard) ∨ yguard = ⊤)
    (h2 : ∀ u ∈ P, ¬ (xguard < (u.1 : ℤ) ∧ u.1 ≤ p.1 ∧ p.2 < u.2 ∧ (u.2 : WithTop ℕ) < yguard))
    (h3 : ∃ u ∈ P, p.1 < u.1 ∧ p.2 < u.2 ∧ (u.2 : WithTop ℕ) < yguard)
    (R : Finset Rect) (hR : IsStrictlyIndependent P R) :
    ∃ R' : Finset Rect, R ⊆ R' ∧ IsStrictlyIndependent P R' ∧
      ∃ q ∈ P, p.1 < q.1 ∧ p.2 < q.2 ∧ (q.2 : WithTop ℕ) < yguard ∧ (p, q) ∈ R' := by sorry

end ChaChaTree.DynOpt
