-- Prove2me | Theorems.Thm_Disjunctive_Polarity_full_rank_face_dimension_preserved
-- name    : Disjunctive.Polarity.full_rank_face_dimension_preserved
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:18:48.489364+00:00
-- url     : https://prove2.me/theorems/831eea04-c8b5-4e30-bdba-7db3906ed5e9
-- title:
--   Corollary 2.10 — faces under a full column rank projection
-- statement:
--   This is Corollary 2.10 of Balas's *Disjunctive Programming*, a consequence of Theorem 2.7 for
--   the dimension-preserving case.
--
--   If $A_=$ has full column rank ($r^* = p$), then every $d$-dimensional face $F_c$ of $Q$, for
--   $0 \le d \le \dim(Q) - 1$, projects to a $d$-dimensional face of $\mathrm{Proj}_x(Q)$:
--   $\mathrm{Proj}_x(F_c)$ is again a face of $\mathrm{Proj}_x(Q)$, of the same dimension $d$.
--
--   Unlike Corollary 2.9, no rank-matching hypothesis on $F_c$ itself is needed here — full column
--   rank of $A_=$ for $Q$ as a whole is already enough to make every face's projection well-behaved.
--
--   **Formalization Note.** "Face" here is Mathlib's `IsExtreme` (no codimension restriction, unlike
--   `IsFacet`), matching the book's unrestricted "$d$-dimensional face" for any $0 \le d \le
--   \dim(Q)-1$.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 30, Corollary 2.10

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection
import Definitions.Def_Disjunctive_Polarity_EqualitySubsystem

namespace Disjunctive.Polarity

/-- Corollary 2.10 (Balas §2.2.3, p. 30): if `A=` has full column rank, every `d`-dimensional
face of `Q` (for `0 ≤ d ≤ dim(Q) - 1`) projects to a `d`-dimensional face of `Proj_x(Q)`. -/
theorem full_rank_face_dimension_preserved {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (hFullRank : EqRankA A B b = p)
    (Fc : Set ((Fin p → ℝ) × (Fin q → ℝ))) (hFace : IsExtreme ℝ (Poly2 A B b) Fc)
    (d : ℕ) (hd : (d : ℤ) ≤ PolyDim (Poly2 A B b) - 1) (hdimFc : PolyDim Fc = (d : ℤ)) :
    IsExtreme ℝ (ProjOntoX (Poly2 A B b)) (ProjOntoX Fc) ∧ PolyDim (ProjOntoX Fc) = (d : ℤ) := by sorry

end Disjunctive.Polarity
