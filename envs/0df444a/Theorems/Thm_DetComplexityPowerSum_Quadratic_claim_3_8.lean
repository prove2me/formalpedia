-- Prove2me | Theorems.Thm_DetComplexityPowerSum_Quadratic_claim_3_8
-- name    : DetComplexityPowerSum.Quadratic.claim_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:36:44.018927+00:00
-- url     : https://prove2.me/theorems/a8ffa709-47c8-48e8-903d-a99aec39a466
-- title:
--   Claim 3.8 — the proxy system projects into $S$
-- statement:
--   Let $n\ge 2$, $\det M(x)=\sum_{i=1}^nx_i^n$, and let $g,h$ be as in Claim 3.6. If $(a,b,c)\in T$, then $a\in S$.
--
--   Here $T$ is the solution set of Definition 3.7 and $S$ that of Definition 2.2. The claim shows that the proxy system does not create points outside the original system.
--
--   Differences from the source:
--   - encoding: $g,h$ are the vectors picked in Claim 3.6 → any $g,h$ with `NormalizesKernels`; reason: the source's pick is an arbitrary pair with this property, so no instance changes
--   - encoding: 1-based coordinates $x_{n-1}$ and $i\le n-2$ → 0-based `Fin n` with `IsPenultimate` (`i + 2 = n`) and `IsEarly` (`i + 2 < n`); reason: the same coordinates under the shift by one
-- source:
--   Mrinal Kumar, Ben Lee Volk, STOC 2027 submission #131 (October 2026), p. 7, Claim 3.8

import Mathlib
import Definitions.Def_PermanentCubic
import Definitions.Def_DetComplexityPowerSum_Quadratic_ProxySystem
open OAI.PermanentBorder

namespace DetComplexityPowerSum.Quadratic

theorem claim_3_8 {n m : ℕ} (M₀ : Matrix (Fin m) (Fin m) ℂ)
    (M : Fin n → Matrix (Fin m) (Fin m) ℂ) (hn : 2 ≤ n)
    (hrep : affineMatrixPolynomial m M₀ M = powerSum n)
    (g h : Fin m → ℂ) (hgh : NormalizesKernels M₀ M g h)
    {a : Fin n → ℂ} {b c : Fin m → ℂ} (habc : (a, b, c) ∈ proxySystem M₀ M g h) :
    a ∈ polarSlice n := by sorry

end DetComplexityPowerSum.Quadratic
