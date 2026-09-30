-- Prove2me | Theorems.Thm_ArrowDebreu_ThmI_Yhat_bounded
-- name    : ArrowDebreu.ThmI.Yhat_bounded
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:41:54.59075+00:00
-- url     : https://prove2.me/theorems/3b88df6a-1d51-4c18-9e4b-bd832a5dc5ee
-- title:
--   Attainable production plans are bounded (§3.3.1 (7))
-- statement:
--   Let an economy satisfy Assumptions I.a, I.b, I.c and II. For each producer $j$ let $\hat Y_j$ be the set of **attainable** production plans: those $y_j \in Y_j$ for which there are $x_i \in X_i$ (every $i$) and $y_{j'} \in Y_{j'}$ ($j' \ne j$) with
--   $$z = \sum_i x_i - \sum_j y_j - \sum_i \zeta_i \leqq 0.$$
--   Then $\hat Y_j$ is a bounded subset of $\mathbb R^l$ for every $j$.
--
--   Together with the boundedness of the attainable consumption sets, this allows the economy to be truncated to a large cube without changing its equilibria.
-- source:
--   Arrow & Debreu, Existence of an Equilibrium for a Competitive Economy, Econometrica 22 (1954), https://doi.org/10.2307/1907353, pp. 276–277 (PDF pp. 13–14), §3.3.1, display (7); Ŷ_j defined in §3.3.0

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmI_economyE
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

/-- **§3.3.1, display (7)**, Arrow & Debreu, Econometrica 22 (1954), p. 277 (PDF p. 14): "`Ŷ_j` is
bounded for all `j`", where `Ŷ_j` (§3.3.0, p. 276) is the set of production plans `y_j ∈ Y_j`
that can be completed by `x_i ∈ X_i` (all `i`) and `y_{j'} ∈ Y_{j'}` (`j' ≠ j`) with
`z = Σ_i x_i − Σ_j y_j − ζ ≦ 0`.

**Formalization Note.** The argument of §3.3.1 uses Assumptions I.a, I.b, I.c and II; these are
the hypotheses. Boundedness is Mathlib's `Bornology.IsBounded` in `R^l` (sup-norm, equivalent to
the Euclidean one). -/
theorem Yhat_bounded {l m n : ℕ} (E : Economy l m n) (hIa : AssumptionIa E) (hIb : AssumptionIb E)
    (hIc : AssumptionIc E) (hII : AssumptionII E) :
    ∀ j, Bornology.IsBounded (Yhat E j) := by sorry

end ArrowDebreu.ThmI
