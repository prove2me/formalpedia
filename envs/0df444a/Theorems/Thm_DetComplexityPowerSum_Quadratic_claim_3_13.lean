-- Prove2me | Theorems.Thm_DetComplexityPowerSum_Quadratic_claim_3_13
-- name    : DetComplexityPowerSum.Quadratic.claim_3_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:40:54.352951+00:00
-- url     : https://prove2.me/theorems/17cd2df6-f2b1-405b-a9ae-6b99924c304a
-- title:
--   Claim 3.13 — the amended system has the same size: $|T|=|T'|$
-- statement:
--   Let $n\ge 2$, $\det M(x)=\sum_{i=1}^nx_i^n$, let $g,h$ be as in Claim 3.6 and let $q,\Gamma$ be as in Definition 3.12. Then
--   $$|T|=|T'|.$$
--
--   Here $T'$ is the solution set of Definition 3.12. Passing to the square system therefore loses no solutions and creates none.
--
--   **Formalization Note** Finiteness of $T'$ is stated together with the equality, since `Set.ncard` is $0$ on an infinite set; $T$ is finite by Corollary 3.10.
--
--   Differences from the source:
--   - encoding: $|T|=|T'|$ → `T'.Finite` together with equality of `Set.ncard`; reason: `ncard` is a default on infinite sets; $T$ is finite, so equal size forces $T'$ finite
--   - encoding: $g,h$ are the vectors picked in Claim 3.6 → any $g,h$ with `NormalizesKernels`; reason: the source's pick is an arbitrary pair with this property, so no instance changes
--   - encoding: $q,\Gamma$ are picked in Definition 3.12 → any $q,\Gamma$ with `IsAmendmentData`; reason: the source's pick is an arbitrary pair with this property, so no instance changes
--   - encoding: 1-based coordinates $x_{n-1}$ and $i\le n-2$ → 0-based `Fin n` with `IsPenultimate` (`i + 2 = n`) and `IsEarly` (`i + 2 < n`); reason: the same coordinates under the shift by one
-- source:
--   Mrinal Kumar, Ben Lee Volk, STOC 2027 submission #131 (October 2026), p. 9, Claim 3.13

import Mathlib
import Definitions.Def_PermanentCubic
import Definitions.Def_DetComplexityPowerSum_Quadratic_AmendedProxySystem
open OAI.PermanentBorder

namespace DetComplexityPowerSum.Quadratic

theorem claim_3_13 {n m : ℕ} (M₀ : Matrix (Fin m) (Fin m) ℂ)
    (M : Fin n → Matrix (Fin m) (Fin m) ℂ) (hn : 2 ≤ n)
    (hrep : affineMatrixPolynomial m M₀ M = powerSum n)
    (g h : Fin m → ℂ) (hgh : NormalizesKernels M₀ M g h)
    (q : Fin m → ℂ) (Γ : Matrix (Fin (m - 1)) (Fin m) ℂ)
    (hqΓ : IsAmendmentData M₀ M g h q Γ) :
    (amendedProxySystem M₀ M g h q Γ).Finite ∧
      (proxySystem M₀ M g h).ncard = (amendedProxySystem M₀ M g h q Γ).ncard := by sorry

end DetComplexityPowerSum.Quadratic
