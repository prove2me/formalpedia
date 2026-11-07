-- Prove2me | Theorems.Thm_ClawFreeChoosable_corollary_8_4_cobipartite_satisfies_M
-- name    : ClawFreeChoosable.corollary_8_4_cobipartite_satisfies_M
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:46:30.556675+00:00
-- url     : https://prove2.me/theorems/db46ae28-4b99-43a6-ac10-fa30ae5699af
-- title:
--   Corollary 8.4 — cobipartite graphs satisfy (Mk)
-- statement:
--   Every finite cobipartite graph $H$ satisfies the mixed-list property (Mk) for every integer $k \ge \omega(H)$.
--
--   This is the form in which Theorem 8.3 is used when a nonempty precoloured clique is attached to a cobipartite atom.
--
--   Differences from the source:
--   - encoding: (Pk)/(Mk) are defined for an integer k ≥ ω(H) → k : ℕ with the hypothesis cliqueNum ≤ k, the property itself not bundling it; reason: Lean convention; same instances
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, Corollary 8.4, p.17 (PDF p.20)

import Mathlib
import Definitions.Def_ClawFreeChoosable_IsCobipartite
import Definitions.Def_ClawFreeChoosable_SatisfiesM

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **Corollary 8.4** (Mishra, Narayanan N, Shankar, *Claw-free perfect graphs are chromatic-choosable*, arXiv:2611.01068v1, p.17): every cobipartite graph `H` satisfies (Mk) for every integer
`k ≥ ω(H)`. -/
theorem corollary_8_4_cobipartite_satisfies_M {V : Type} [Fintype V] (H : SimpleGraph V)
    (hH : IsCobipartite H) (k : ℕ) (hk : H.cliqueNum ≤ k) : SatisfiesM H k := by sorry

end ClawFreeChoosable
