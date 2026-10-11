-- Prove2me | Theorems.Thm_CarneiroDeSitter_dust_phase_asymptotics
-- name    : CarneiroDeSitter.dust_phase_asymptotics
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T02:19:37.951981+00:00
-- url     : https://prove2.me/theorems/7aa7463f-8ac7-42ad-92ab-aea5c2bcc704
-- title:
--   p. 2245–2246: the dust solution starts as $a\propto t^{2/3}$ and tends to de Sitter with $H\to\sigma/3$
-- statement:
--   Let $C>0$, $\sigma>0$ and $a(t)=C(e^{\sigma t/2}-1)^{2/3}$ (Eq. (14)). Then
--
--   1. (Einstein–de Sitter start) as $t\to0^+$,
--   $$
--   a(t)\sim C\Big(\frac\sigma2\Big)^{2/3}t^{2/3};
--   $$
--   2. (de Sitter end) the Hubble parameter $H=\dot a/a$ satisfies
--   $$
--   \lim_{t\to\infty}H(t)=\frac\sigma3 ,
--   $$
--   the value fixed by $3H^2=\Lambda=\sigma H$.
--
--   **Formalization Note** $\sim$ is `Asymptotics.IsEquivalent` along $t\to0^+$, and $t^{2/3}$ is the real power function.
-- source:
--   S. Carneiro, "From de Sitter to de Sitter: a non-singular inflationary universe driven by vacuum", Int. J. Mod. Phys. D 15 (2006) 2241-2247, https://doi.org/10.1142/S0218271806009510, p. 2245 (paragraph after Eq. (14)) and p. 2246 (de Sitter limit)

import Mathlib
import Definitions.Def_CarneiroDeSitter2006

open Real Filter Topology Asymptotics MeasureTheory Set

namespace CarneiroDeSitter

theorem dust_phase_asymptotics (C σ : ℝ) (hC : 0 < C) (hσ : 0 < σ) :
    dustScaleFactor C σ ~[𝓝[>] 0] (fun t => C * (σ / 2) ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3)) ∧
    Tendsto (fun t => deriv (dustScaleFactor C σ) t / dustScaleFactor C σ t) atTop
      (𝓝 (σ / 3)) := by sorry

end CarneiroDeSitter
