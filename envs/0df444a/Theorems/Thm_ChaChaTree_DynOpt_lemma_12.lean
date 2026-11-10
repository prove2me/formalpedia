-- Prove2me | Theorems.Thm_ChaChaTree_DynOpt_lemma_12
-- name    : ChaChaTree.DynOpt.lemma_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:22:38.07929+00:00
-- url     : https://prove2.me/theorems/df39886b-a4bb-420b-8356-77d0a7ff28a9
-- title:
--   Lemma 12 — four sufficient conditions for two input-free rectangles to be strictly independent
-- statement:
--   Let $P$ be an instance and $r_1, r_2$ two input-free rectangles on it. Then the two rectangles are strictly independent (the set $\{r_1, r_2\}$ satisfies Definition 11) if at least one of the following holds:
--   * the two rectangles share a defining point;
--   * $r_1$ is right and $r_2$ left, or vice versa;
--   * $r_1$ contains no corner of $r_2$;
--   * $r_2$ contains no corner of $r_1$.
--
--   Differences from the source:
--   - encoding: a rectangle □_{p,q} → the ordered pair (p, q) : Rect with IsRectOn P (p, q); reason: a rectangle is determined by its two defining points with p.y < q.y; same objects
--   - encoding: the two rectangles are strictly independent → IsStrictlyIndependent P {r₁, r₂}; reason: Definition 11 applied to the set of the two rectangles; when r₁ = r₂ the set is a single input-free rectangle, which the definition also accepts
-- source:
--   Čech, Haeupler, Roeyskoe, Rozhoň, Tarjan, Yingchareonthawornchai, Dynamic Optimality to within O(log log log n), STOC 2027 submission (manuscript, sha256 9316fbfd…7b9e), Lemma 12, p. 15 (PDF 16)

import Mathlib
import Definitions.Def_ChaChaTree_DynOpt_Instance
import Definitions.Def_ChaChaTree_DynOpt_Rectangles

set_option autoImplicit false

namespace ChaChaTree.DynOpt

/-- **Lemma 12** (p. 15). Two input-free rectangles `r₁`, `r₂` on an instance `P` are strictly
independent if they share a defining point, or one is right and the other left, or `r₁`
contains no corner of `r₂`, or `r₂` contains no corner of `r₁`. -/
theorem lemma_12 (N T : ℕ) (P : Finset (ℕ × ℕ)) (hP : IsInstance N T P) (r₁ r₂ : Rect)
    (h₁ : IsRectOn P r₁ ∧ InputFree P r₁) (h₂ : IsRectOn P r₂ ∧ InputFree P r₂)
    (h : ShareDefiningPoint r₁ r₂ ∨ (IsRightRect r₁ ∧ IsLeftRect r₂) ∨
      (IsLeftRect r₁ ∧ IsRightRect r₂) ∨ (∀ c ∈ corners r₂, ¬ RContains r₁ c) ∨
      (∀ c ∈ corners r₁, ¬ RContains r₂ c)) :
    IsStrictlyIndependent P {r₁, r₂} := by sorry

end ChaChaTree.DynOpt
