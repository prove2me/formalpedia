-- Prove2me | Theorems.Thm_ArrowDebreu_ThmI_Xhat_bounded
-- name    : ArrowDebreu.ThmI.Xhat_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:42:24.562212+00:00
-- url     : https://prove2.me/theorems/749c3548-d086-494d-8be5-a06fb7878a9e
-- title:
--   Attainable consumption vectors are bounded (§3.3.2 (2))
-- statement:
--   Let an economy satisfy Assumptions I.a, I.b, I.c and II. For each consumer $i$ let $\hat X_i$ be the set of **attainable** consumption vectors: those $x_i \in X_i$ for which there are $x_{i'} \in X_{i'}$ ($i' \ne i$) and $y_j \in Y_j$ (every $j$) with
--   $$z = \sum_i x_i - \sum_j y_j - \sum_i \zeta_i \leqq 0.$$
--   Then $\hat X_i$ is a bounded subset of $\mathbb R^l$ for every $i$.
--
--   With the boundedness of the attainable production plans, this is what permits the choice of a cube $C$ containing all attainable choices in its interior.
-- source:
--   Arrow & Debreu, Existence of an Equilibrium for a Competitive Economy, Econometrica 22 (1954), https://doi.org/10.2307/1907353, p. 277 (PDF p. 14), §3.3.2, display (2); X̂_i defined in §3.3.0

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmI_economyE
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

/-- **§3.3.2, display (2)**, Arrow & Debreu, Econometrica 22 (1954), p. 277 (PDF p. 14): "`X̂_i` is
bounded for all `i`", where `X̂_i` (§3.3.0, p. 276) is the set of consumption vectors `x_i ∈ X_i`
that can be completed by `x_{i'} ∈ X_{i'}` (`i' ≠ i`) and `y_j ∈ Y_j` (all `j`) with
`z = Σ_i x_i − Σ_j y_j − ζ ≦ 0`.

**Formalization Note.** §3.3.2 uses Assumption II and display (7) of §3.3.1, which rests on
I.a, I.b, I.c and II; these are the hypotheses. -/
theorem Xhat_bounded {l m n : ℕ} (E : Economy l m n) (hIa : AssumptionIa E) (hIb : AssumptionIb E)
    (hIc : AssumptionIc E) (hII : AssumptionII E) :
    ∀ i, Bornology.IsBounded (Xhat E i) := by sorry

end ArrowDebreu.ThmI
