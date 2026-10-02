-- Prove2me | Theorems.Thm_Disjunctive_Polarity_reverse_polar_scaled_stabilizes
-- name    : Disjunctive.Polarity.reverse_polar_scaled_stabilizes
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:22:20.096081+00:00
-- url     : https://prove2.me/theorems/490118ce-0888-4346-9a5c-c0b88abe96c0
-- title:
--   Theorem 2.16 — stabilization of the scaled reverse polar
-- statement:
--   This is Theorem 2.16 of Balas's *Disjunctive Programming*, the technical bridge that lets
--   Corollary 2.17 relate the polarity route to the projection cone $W_0$.
--
--   For any set $F$ and scaling factor $\alpha_0$, writing $F_{(\alpha_0)}$ for the scaled polar and
--   iterating it at the *same* $\alpha_0$ each time:
--
--   $$
--   F_{(\alpha_0)}^{\#\#\#} = F_{(\alpha_0)}^{\#},
--   $$
--
--   i.e. three applications of the scaled-polar operator (at fixed $\alpha_0$) equal one application.
--   The proof splits on the sign of $\alpha_0$: for $\alpha_0 \le 0$ it reduces to the ordinary
--   polar's involution identity, and for $\alpha_0 > 0$ it follows from Theorem 2.14 applied to
--   $F_{(\alpha_0)}$ itself (with the two sub-cases $0 \in \mathrm{cl}\,\mathrm{conv}(F)$ and
--   $0 \notin \mathrm{cl}\,\mathrm{conv}(F)$).
--
--   **Formalization Note.** Iterating `ScaledPolar` at a fixed `α0` (rather than switching to the
--   unscaled reverse polar after the first application) is confirmed against Example 1's own worked
--   computation of $F^{\#\#}_{(-1)}$ in the text — see `MODERATION_NOTES.md`.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 34, Theorem 2.16

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Polars

namespace Disjunctive.Polarity

/-- Theorem 2.16 (Balas §2.4, p. 34): the scaled reverse polar stabilizes after two
applications: `F###_(α₀) = F#_(α₀)`, where each `#` reapplies `ScaledPolar` at the *same*
scaling factor `α₀` (matching Example 1's computation, e.g. `F##_(-1)` uses `α₀ = -1` again in
the second application, not the unscaled `α₀ = 1`). -/
theorem reverse_polar_scaled_stabilizes {n : ℕ} (F : Set (Fin n → ℝ)) (α0 : ℝ) :
    ScaledPolar (ScaledPolar (ScaledPolar F α0) α0) α0 = ScaledPolar F α0 := by sorry

end Disjunctive.Polarity
