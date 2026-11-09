-- Prove2me | Theorems.Thm_DetComplexityPowerSum_Quadratic_exists_amendment_data
-- name    : DetComplexityPowerSum.Quadratic.exists_amendment_data
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:41:24.775984+00:00
-- url     : https://prove2.me/theorems/95041049-4cff-4372-af11-e7bf26bf891f
-- title:
--   Definition 3.12 — amendment data $q,\Gamma$ exists
-- statement:
--   Let $n\ge 2$, $\det M(x)=\sum_{i=1}^nx_i^n$, and let $g,h$ be as in Claim 3.6. Then there exist a vector $q\in\mathbb C^m$ and a matrix $\Gamma\in\mathbb C^{(m-1)\times m}$ such that $b^Tq\ne 0$ for every $b$ for which there exist $a,c$ with $(a,b,c)\in T$, and $\ker\Gamma=\operatorname{span}\{q\}$.
--
--   Definition 3.12 asserts that this choice is possible. It is stated separately so that the hypotheses of Claim 3.13 and Lemma 3.14 are known to be satisfiable. It is a supporting item and carries no result number of its own.
--
--   Differences from the source:
--   - encoding: $g,h$ are the vectors picked in Claim 3.6 → any $g,h$ with `NormalizesKernels`; reason: the source's pick is an arbitrary pair with this property, so no instance changes
--   - encoding: 1-based coordinates $x_{n-1}$ and $i\le n-2$ → 0-based `Fin n` with `IsPenultimate` (`i + 2 = n`) and `IsEarly` (`i + 2 < n`); reason: the same coordinates under the shift by one
-- source:
--   Mrinal Kumar, Ben Lee Volk, STOC 2027 submission #131 (October 2026), p. 9, Definition 3.12 (existence of $q$ and $\Gamma$)

import Mathlib
import Definitions.Def_PermanentCubic
import Definitions.Def_DetComplexityPowerSum_Quadratic_AmendedProxySystem
open OAI.PermanentBorder

namespace DetComplexityPowerSum.Quadratic

theorem exists_amendment_data {n m : ℕ} (M₀ : Matrix (Fin m) (Fin m) ℂ)
    (M : Fin n → Matrix (Fin m) (Fin m) ℂ) (hn : 2 ≤ n)
    (hrep : affineMatrixPolynomial m M₀ M = powerSum n)
    (g h : Fin m → ℂ) (hgh : NormalizesKernels M₀ M g h) :
    ∃ (q : Fin m → ℂ) (Γ : Matrix (Fin (m - 1)) (Fin m) ℂ),
      IsAmendmentData M₀ M g h q Γ := by sorry

end DetComplexityPowerSum.Quadratic
