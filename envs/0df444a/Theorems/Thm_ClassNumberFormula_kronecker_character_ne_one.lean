-- Prove2me | Theorems.Thm_ClassNumberFormula_kronecker_character_ne_one
-- name    : ClassNumberFormula.kronecker_character_ne_one
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T03:50:33.937489+00:00
-- url     : https://prove2.me/theorems/52a2bf83-c7af-4d39-a4b6-67844d3d52a9
-- title:
--   The Kronecker character of a quadratic field is nontrivial: $\chi \ne 1$
-- statement:
--   With $K$, $d$ and $\chi$ as in the quadratic factorisation milestone, the character $\chi$ is not the trivial character. Indeed $K$ is a genuine quadratic field, so its discriminant satisfies $|d|>1$; a fundamental discriminant with $|d|>1$ takes the value $-1$ at some integer (the Kronecker symbol is a nonprincipal real character), hence $\chi$ differs from $1$. Nontriviality is the exact hypothesis that makes $L(s,\chi)$ holomorphic at $s=1$, which the residue transport consumes.
-- source:
--   Mission 'Class Number Formula' (cc969585), milestone b3130a32 quadratic_dedekindZeta_eq_zeta_mul_L; Davenport, Multiplicative Number Theory, Ch. 6; Wikipedia 'Class number formula' rev 1366411311

import Mathlib
import Definitions.Def_ClassNumberFormula_Kronecker
open NumberField NumberField.InfinitePlace NumberField.Units Filter Topology Real

namespace ClassNumberFormula

theorem kronecker_character_ne_one (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [NeZero (discr K).natAbs]
    (χ : DirichletCharacter ℂ (discr K).natAbs)
    (hχ : ∀ n : ℕ, χ n = (kroneckerSymbol (discr K) n : ℂ)) :
    χ ≠ 1 := by sorry

end ClassNumberFormula
