-- Prove2me | Theorems.Thm_DetComplexityPowerSum_Quadratic_lemma_3_14
-- name    : DetComplexityPowerSum.Quadratic.lemma_3_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:41:05.618805+00:00
-- url     : https://prove2.me/theorems/8db26197-b1a2-425d-9c9f-f53e9663411d
-- title:
--   Lemma 3.14 — $|T'|\le 2^{n-2}\bigl(e(2m-1)/(n-1)\bigr)^{n-1}$
-- statement:
--   Let $n\ge 2$, $\det M(x)=\sum_{i=1}^nx_i^n$, let $g,h$ be as in Claim 3.6 and let $q,\Gamma$ be as in Definition 3.12. The size of $T'$, that is, the number of solutions to the system in Definition 3.12, is at most
--   $$2^{n-2}\cdot\left(\frac{e(2m-1)}{n-1}\right)^{n-1}.$$
--
--   Every point of $T'$ is counted, not only simple roots. Together with $|T'|=|T|=|S|\ge(n-1)^{n-2}$ this bound forces $m=\Omega(n^2)$.
--
--   **Formalization Note** The bound is an expression in $\mathbb R$, with $e$ written `Real.exp 1` and $n$, $m$ cast to reals before the subtraction and the division; $n\ge 2$ keeps the denominator positive.
--
--   Differences from the source:
--   - encoding: the size of $T'$ is at most the bound → `T'.Finite` together with a bound on `Set.ncard`; reason: `ncard` is a default on infinite sets, so finiteness is written out
--   - encoding: $g,h$ are the vectors picked in Claim 3.6 → any $g,h$ with `NormalizesKernels`; reason: the source's pick is an arbitrary pair with this property, so no instance changes
--   - encoding: $q,\Gamma$ are picked in Definition 3.12 → any $q,\Gamma$ with `IsAmendmentData`; reason: the source's pick is an arbitrary pair with this property, so no instance changes
--   - encoding: 1-based coordinates $x_{n-1}$ and $i\le n-2$ → 0-based `Fin n` with `IsPenultimate` (`i + 2 = n`) and `IsEarly` (`i + 2 < n`); reason: the same coordinates under the shift by one
-- source:
--   Mrinal Kumar, Ben Lee Volk, STOC 2027 submission #131 (October 2026), p. 10, Lemma 3.14

import Mathlib
import Definitions.Def_PermanentCubic
import Definitions.Def_DetComplexityPowerSum_Quadratic_AmendedProxySystem
open OAI.PermanentBorder

namespace DetComplexityPowerSum.Quadratic

theorem lemma_3_14 {n m : ℕ} (M₀ : Matrix (Fin m) (Fin m) ℂ)
    (M : Fin n → Matrix (Fin m) (Fin m) ℂ) (hn : 2 ≤ n)
    (hrep : affineMatrixPolynomial m M₀ M = powerSum n)
    (g h : Fin m → ℂ) (hgh : NormalizesKernels M₀ M g h)
    (q : Fin m → ℂ) (Γ : Matrix (Fin (m - 1)) (Fin m) ℂ)
    (hqΓ : IsAmendmentData M₀ M g h q Γ) :
    (amendedProxySystem M₀ M g h q Γ).Finite ∧
      ((amendedProxySystem M₀ M g h q Γ).ncard : ℝ) ≤
        2 ^ (n - 2) * (Real.exp 1 * (2 * (m : ℝ) - 1) / ((n : ℝ) - 1)) ^ (n - 1) := by sorry

end DetComplexityPowerSum.Quadratic
