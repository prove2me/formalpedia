-- Prove2me | Theorems.Thm_ArrowDebreu_ThmII_XhatPrime_YhatPrime_bounded
-- name    : ArrowDebreu.ThmII.XhatPrime_YhatPrime_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T22:19:46.262014+00:00
-- url     : https://prove2.me/theorems/e334e3b5-7dc3-448e-b2d0-adff29586a64
-- title:
--   The sets $\hat X'_i$ and $\hat Y'_j$ are bounded
-- statement:
--   Consider an economy satisfying Assumptions I–III, IV′, VI and VII, and lower bounds $\xi_i$ of the consumption sets. Then the sets
--   $$\hat X'_i=\{x_i\in X_i:\ \exists\,x_{i'}\in X_{i'}\ (i'\ne i),\ y_j\in Y_j,\ x-y\leqq\zeta'\},\qquad \hat Y'_j=\{y_j\in Y_j:\ \exists\,x_i\in X_i,\ y_{j'}\in Y_{j'}\ (j'\ne j),\ x-y\leqq\zeta'\}$$
--   are bounded, for every consumer $i$ and every producer $j$.
--
--   These are the sets of Theorem I's proof with $\zeta$ replaced by $\zeta'$. Their boundedness is what allows a cube $C'$ containing them all in its interior.
--
--   **Formalization Note** Boundedness is Mathlib's `Bornology.IsBounded` on `Fin l → ℝ`. Assumption V is not assumed.
-- source:
--   Arrow & Debreu, Econometrica 22 (1954), https://doi.org/10.2307/1907353, p. 284 (PDF p. 21), §5.2.0 (repeating §3.3.0–§3.3.3)

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_ThmII_AssumptionsII
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmII_economyEeps
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmII

/-- **§5.2.0** (Arrow & Debreu, Econometrica 22 (1954), §5.2.0, p. 284, PDF p. 21). For an economic
system satisfying Assumptions I–III, IV′, VI and VII
(Assumption V, which the paper uses only in §5.3.5, is not assumed) and lower bounds `ξ_i` of the consumption sets as
in Assumption II, the sets `X̂'_i` and `Ŷ'_j` of §5.2.0 (defined like `X̂_i`, `Ŷ_j` of §3.3.0 with
`ζ` replaced by `ζ'`) are bounded, for every `i` and every `j`. The paper states this as "the
arguments of 3.3.0.–.3. may therefore be repeated exactly", which is what makes the choice of the
cube `C'` possible.

**Formalization Note.** Boundedness is Mathlib's `Bornology.IsBounded` for the sup metric on
`Fin l → ℝ`, equivalent to boundedness in the Euclidean norm. -/
theorem XhatPrime_YhatPrime_bounded {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsIIexceptV E)
    (ξ : Fin m → Fin l → ℝ) (hξ : ∀ i, ∀ x ∈ E.X i, ξ i ≤ x) :
    (∀ i, Bornology.IsBounded (XhatPrime E ξ i)) ∧ ∀ j, Bornology.IsBounded (YhatPrime E ξ j) := by sorry

end ArrowDebreu.ThmII
