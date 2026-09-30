-- Prove2me | Theorems.Thm_ArrowDebreu_ThmII_theorem_II
-- name    : ArrowDebreu.ThmII.theorem_II
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T22:35:00.495468+00:00
-- url     : https://prove2.me/theorems/2a9005f7-6b7c-40ca-9558-e2c210f94f38
-- title:
--   Arrow–Debreu Theorem II — existence of a competitive equilibrium when every consumer can supply productive labor
-- statement:
--   Let an economy with $l$ commodities, $n$ producers and $m$ consumers satisfy Assumptions I–III, IV′ and V–VII:
--
--   1. production sets are closed, convex and contain $0$, and the aggregate production set $Y$ admits no free production and no reversible production (I);
--   2. consumption sets are closed, convex and bounded below (II);
--   3. utilities are continuous, nonsatiated and satisfy the strict convexity condition III.c (III);
--   4. every consumer can, while staying in the consumption set, keep every holding at or below the endowment and supply a positive amount of at least one type of productive labor (IV′.a), and profit shares are nonnegative and sum to one (IV.b);
--   5. an excess supply of every commodity can be arranged (V);
--   6. some commodity is always desired by every consumer (VI), and some type of productive labor exists (VII).
--
--   Then there is a competitive equilibrium: vectors $x_1^*,\dots,x_m^*,y_1^*,\dots,y_n^*,p^*$ satisfying Conditions 1–4,
--   $$\exists\,(x^*,y^*,p^*)\ \text{competitive equilibrium}.$$
--
--   Theorem I required every consumer to hold initially a positive amount of every good (IV.a). Theorem II drops that requirement: it only asks that each consumer be able to supply some labor that is always productive of a desired good.
--
--   **Formalization Note** Assumption VII makes the commodity set nonempty, so $l\ge1$ is not a separate hypothesis. Assumption IV.a is not assumed.
-- source:
--   Arrow & Debreu, Existence of an Equilibrium for a Competitive Economy, Econometrica 22 (1954), https://doi.org/10.2307/1907353, p. 281 (PDF p. 18), §4.5, Theorem II

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_ThmII_AssumptionsII
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmII

/-- **Theorem II** (Arrow & Debreu, *Existence of an Equilibrium for a Competitive Economy*,
Econometrica 22 (1954), §4.5, p. 281, PDF p. 18): for an economic system satisfying Assumptions
I–III, IV′, and V–VII, there is a competitive equilibrium — vectors
`(x_1^*, ⋯, x_m^*, y_1^*, ⋯, y_n^*, p^*)` satisfying Conditions 1–4 (Definition 1.5.0).

**Formalization Note.** The hypotheses are I.a, I.b, I.c, II, III.a–III.c, IV′.a, IV.b, V, VI and
VII (the structure `AssumptionsII`); Assumption IV.a of Theorem I is not assumed. Assumption VII
makes `𝒫`, hence the commodity set, nonempty, so `l ≥ 1` is not a separate hypothesis. -/
theorem theorem_II {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsII E) :
    ∃ (x : Fin m → Fin l → ℝ) (y : Fin n → Fin l → ℝ) (p : Fin l → ℝ),
      IsCompetitiveEquilibrium E x y p := by sorry

end ArrowDebreu.ThmII
