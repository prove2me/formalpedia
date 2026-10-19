-- Prove2me | Theorems.Thm_CarneiroDeSitter_vacuumTerm_asymptotics
-- name    : CarneiroDeSitter.vacuumTerm_asymptotics
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T02:12:19.679977+00:00
-- url     : https://prove2.me/theorems/712a4b39-b352-43c3-a64a-0e6b3be6180f
-- title:
--   Eq. (11): $\Lambda=(m+H)^4-m^4\sim H^4$ for $H\gg m$ and $\sim 4m^3H$ for $H\ll m$
-- statement:
--   Let $m>0$ and $\Lambda(H)=(m+H)^4-m^4$ (Eq. (11)). Then
--
--   1. as $H\to+\infty$, $\displaystyle \Lambda(H)\sim H^4$, i.e. $\Lambda(H)/H^4\to1$;
--   2. as $H\to0^+$, $\displaystyle \Lambda(H)\sim 4m^3H$, i.e. $\Lambda(H)/(4m^3H)\to1$.
--
--   These are the two regimes of the vacuum term: the cutoff-independent early-time law $\Lambda\approx H^4$ that drives the non-singular inflationary phase, and the late-time law $\Lambda\approx m^3H$ that governs the dust era.
--
--   **Formalization Note** $f\sim g$ is Mathlib's asymptotic equivalence `Asymptotics.IsEquivalent`; the second limit is taken from the right of $0$.
-- source:
--   S. Carneiro, "From de Sitter to de Sitter: a non-singular inflationary universe driven by vacuum", Int. J. Mod. Phys. D 15 (2006) 2241-2247, https://doi.org/10.1142/S0218271806009510, p. 2244, Eq. (11) and the following paragraph

import Mathlib
import Definitions.Def_CarneiroDeSitter2006

open Real Filter Topology Asymptotics MeasureTheory Set

namespace CarneiroDeSitter

theorem vacuumTerm_asymptotics (m : ℝ) (hm : 0 < m) :
    (fun H => vacuumTerm m H) ~[atTop] (fun H => H ^ 4) ∧
    (fun H => vacuumTerm m H) ~[𝓝[>] 0] (fun H => 4 * m ^ 3 * H) := by sorry

end CarneiroDeSitter
