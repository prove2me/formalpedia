-- Prove2me | Theorems.Thm_Erdos592_galvin_larson_indecomposable
-- name    : Erdos592.galvin_larson_indecomposable
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T18:09:09.131846+00:00
-- url     : https://prove2.me/theorems/56b5df78-f26f-4c29-b7d2-41c230f9188a
-- title:
--   Galvin–Larson: if $\beta\ge3$ and $\omega^\beta\to(\omega^\beta,3)^2$ then $\beta$ is additively indecomposable
-- statement:
--   Let $\beta$ be a countable ordinal with $\beta\ge 3$. If $\omega^\beta$ is a partition ordinal,
--   $$\omega^\beta \to (\omega^\beta, 3)^2,$$
--   then $\beta$ is **additively indecomposable**: for all ordinals $a,b<\beta$ one has $a+b<\beta$. In particular (as $\beta\neq0$), $\beta=\omega^\gamma$ for some countable ordinal $\gamma$.
--
--   This necessary condition, due to Galvin and Larson (1974), reduces Erdős Problem 592 for $\beta\ge3$ to ordinals of the form $\omega^{\omega^\gamma}$.
-- source:
--   T. F. Bloom, Erdős Problem #592, https://www.erdosproblems.com/592 (page last edited 23 January 2026); Lean encoding of the ordinal Ramsey property follows Formal Conjectures, FormalConjecturesForMathlib/SetTheory/Cardinal/SimpleGraph.lean and FormalConjectures/ErdosProblems/592.lean, https://github.com/google-deepmind/formal-conjectures; Galvin and Larson [GaLa74] (F. Galvin, J. Larson, Pinning countable ordinals, Fund. Math., 1974/75)

import Mathlib
import Definitions.Def_Erdos592_Defs

open Cardinal Ordinal

universe u

namespace Erdos592
theorem galvin_larson_indecomposable (β : Ordinal.{u}) (hβ : β.card ≤ ℵ₀) (h3 : 3 ≤ β)
    (h : OrdinalCardinalRamsey (ω ^ β) (ω ^ β) 3) :
    ∀ a < β, ∀ b < β, a + b < β := by sorry
end Erdos592
