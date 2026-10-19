-- Prove2me | Theorems.Thm_CarneiroDeSitter_bose_integral_number_of_states
-- name    : CarneiroDeSitter.bose_integral_number_of_states
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T02:20:00.008194+00:00
-- url     : https://prove2.me/theorems/35dd2cc8-1912-4670-b1ee-20cfc81c464d
-- title:
--   Eq. (15): $\int_0^\infty\frac{\omega^2\,d\omega}{e^{\omega/(m+H)}-1}=2\zeta(3)(m+H)^3$
-- statement:
--   Let $m>0$ and $H\ge0$. Then
--   $$
--   \int_0^\infty\frac{\omega^2}{e^{\omega/(m+H)}-1}\,d\omega=2\,\zeta(3)\,(m+H)^3,\qquad \zeta(3)=\sum_{n\ge1}\frac1{n^3}.
--   $$
--
--   This makes precise the estimate $N\approx V(m+H)^3$ for the number of thermally distributed vacuum states in a volume $V$ (Eq. (15)), which the paper uses to compare the entropy of the initial and final de Sitter phases.
--
--   **Formalization Note** $\zeta(3)$ is written as the series $\sum_{n=0}^\infty 1/(n+1)^3$.
-- source:
--   S. Carneiro, "From de Sitter to de Sitter: a non-singular inflationary universe driven by vacuum", Int. J. Mod. Phys. D 15 (2006) 2241-2247, https://doi.org/10.1142/S0218271806009510, p. 2246, Eq. (15) and the following paragraph

import Mathlib
import Definitions.Def_CarneiroDeSitter2006

open Real Filter Topology Asymptotics MeasureTheory Set

namespace CarneiroDeSitter

theorem bose_integral_number_of_states (m H : ℝ) (hm : 0 < m) (hH : 0 ≤ H) :
    ∫ ω in Ioi (0 : ℝ), ω ^ 2 / (Real.exp (ω / (m + H)) - 1)
      = 2 * (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3) * (m + H) ^ 3 := by sorry

end CarneiroDeSitter
