-- Prove2me | Theorems.Thm_DetComplexityPowerSum_Quadratic_corollary_3_10
-- name    : DetComplexityPowerSum.Quadratic.corollary_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:37:07.149398+00:00
-- url     : https://prove2.me/theorems/d6a075dc-a50a-45b7-9358-942ebabd8e73
-- title:
--   Corollary 3.10 — $T$ is finite and $|T|=|S|$
-- statement:
--   Let $n\ge 2$, $\det M(x)=\sum_{i=1}^nx_i^n$, and let $g,h$ be as in Claim 3.6. Then the set $T$ is finite and
--   $$|T|=|S|.$$
--
--   The proxy system therefore has as many solutions as the original one, and the lower bound of Claim 3.1 transfers to it.
--
--   **Formalization Note** Finiteness is an explicit conclusion, since `Set.ncard` is $0$ on an infinite set.
--
--   Differences from the source:
--   - encoding: $g,h$ are the vectors picked in Claim 3.6 → any $g,h$ with `NormalizesKernels`; reason: the source's pick is an arbitrary pair with this property, so no instance changes
--   - encoding: 1-based coordinates $x_{n-1}$ and $i\le n-2$ → 0-based `Fin n` with `IsPenultimate` (`i + 2 = n`) and `IsEarly` (`i + 2 < n`); reason: the same coordinates under the shift by one
-- source:
--   Mrinal Kumar, Ben Lee Volk, STOC 2027 submission #131 (October 2026), p. 8, Corollary 3.10

import Mathlib
import Definitions.Def_PermanentCubic
import Definitions.Def_DetComplexityPowerSum_Quadratic_ProxySystem
open OAI.PermanentBorder

namespace DetComplexityPowerSum.Quadratic

theorem corollary_3_10 {n m : ℕ} (M₀ : Matrix (Fin m) (Fin m) ℂ)
    (M : Fin n → Matrix (Fin m) (Fin m) ℂ) (hn : 2 ≤ n)
    (hrep : affineMatrixPolynomial m M₀ M = powerSum n)
    (g h : Fin m → ℂ) (hgh : NormalizesKernels M₀ M g h) :
    (proxySystem M₀ M g h).Finite ∧
      (proxySystem M₀ M g h).ncard = (polarSlice n).ncard := by sorry

end DetComplexityPowerSum.Quadratic
