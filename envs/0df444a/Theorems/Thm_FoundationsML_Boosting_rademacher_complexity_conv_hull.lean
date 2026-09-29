-- Prove2me | Theorems.Thm_FoundationsML_Boosting_rademacher_complexity_conv_hull
-- name    : FoundationsML.Boosting.rademacher_complexity_conv_hull
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:10:58.706468+00:00
-- url     : https://prove2.me/theorems/6164818a-5d6b-425e-b557-c7a3ebf65255
-- title:
--   Lemma 7.4 — Rademacher complexity of a convex hull (milestone)
-- statement:
--   **Statement (Lemma 7.4, p. 157, PDF p. 174).** Let $H$ be a set of functions mapping from
--   $X$ to $\mathbb R$. Then, for any sample $S$, $\hat R_S(\mathrm{conv}(H)) = \hat R_S(H)$.
--
--   This is the key structural fact that lets Theorem 5.8's margin bound, applied to
--   $\mathrm{conv}(H)$, be rewritten purely in terms of $H$'s own (typically much smaller)
--   Rademacher complexity — feeding directly into Corollary 7.5.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 157, Lemma 7.4 (PDF p. 174)

import Mathlib
import Definitions.Def_FoundationsML_Boosting_EmpiricalRademacherComplexity
import Definitions.Def_FoundationsML_Boosting_ConvHull

namespace FoundationsML.Boosting

/-- Lemma 7.4 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT
Press 2018, p. 157, PDF p. 174). Let `H` be a set of functions mapping from `X` to `ℝ`. Then,
for any sample `S`, `R̂_S(conv(H)) = R̂_S(H)`. -/
theorem rademacher_complexity_conv_hull {X : Type*} {m : ℕ}
    (H : Set (X → ℝ)) (S : Fin m → X) :
    EmpiricalRademacherComplexity (ConvHull H) S = EmpiricalRademacherComplexity H S := by sorry

end FoundationsML.Boosting
