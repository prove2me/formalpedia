-- Prove2me | Theorems.Thm_DetComplexityPowerSum_Quadratic_claim_3_9
-- name    : DetComplexityPowerSum.Quadratic.claim_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:38:07.988784+00:00
-- url     : https://prove2.me/theorems/9425b25e-3f2d-47ed-b9d4-ebeb590bf990
-- title:
--   Claim 3.9 — every point of $S$ lifts uniquely to $T$
-- statement:
--   Let $n\ge 2$, $\det M(x)=\sum_{i=1}^nx_i^n$, and let $g,h$ be as in Claim 3.6. For every $a\in S$ there are unique $b,c\in\mathbb C^m$ such that $(a,b,c)\in T$.
--
--   Uniqueness is of the pair $(b,c)$ jointly. Together with Claim 3.8 this makes the projection $T\to S$ a bijection.
--
--   Differences from the source:
--   - encoding: $g,h$ are the vectors picked in Claim 3.6 → any $g,h$ with `NormalizesKernels`; reason: the source's pick is an arbitrary pair with this property, so no instance changes
--   - encoding: 1-based coordinates $x_{n-1}$ and $i\le n-2$ → 0-based `Fin n` with `IsPenultimate` (`i + 2 = n`) and `IsEarly` (`i + 2 < n`); reason: the same coordinates under the shift by one
-- source:
--   Mrinal Kumar, Ben Lee Volk, STOC 2027 submission #131 (October 2026), p. 7, Claim 3.9

import Mathlib
import Definitions.Def_PermanentCubic
import Definitions.Def_DetComplexityPowerSum_Quadratic_ProxySystem
open OAI.PermanentBorder

namespace DetComplexityPowerSum.Quadratic

theorem claim_3_9 {n m : ℕ} (M₀ : Matrix (Fin m) (Fin m) ℂ)
    (M : Fin n → Matrix (Fin m) (Fin m) ℂ) (hn : 2 ≤ n)
    (hrep : affineMatrixPolynomial m M₀ M = powerSum n)
    (g h : Fin m → ℂ) (hgh : NormalizesKernels M₀ M g h)
    {a : Fin n → ℂ} (ha : a ∈ polarSlice n) :
    ∃! p : (Fin m → ℂ) × (Fin m → ℂ), (a, p.1, p.2) ∈ proxySystem M₀ M g h := by sorry

end DetComplexityPowerSum.Quadratic
