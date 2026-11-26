-- Prove2me | Theorems.Thm_AME125_reduced_graphState
-- name    : AME125.reduced_graphState
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:45.947046+00:00
-- url     : https://prove2.me/theorems/aeef8c25-283c-5074-80ec-e82249b858fa
-- title:
--   AME125: reduced graph State
-- statement:
--   The entries of the first-`m` reduction of a graph state, as a character sum evaluated:
--   a phase depending only on `a, b`, times `5^(n-m)` if the traced coefficients vanish and `0`
--   otherwise.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L198-L239
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L198-L239

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix

theorem AME125.reduced_graphState {n m : ℕ} (hm : m ≤ n) (U : Matrix (Fin n) (Fin n) (ZMod 5))
    (a b : Config m 5) :
    ∃ K : ZMod 5, (toZ a = toZ b → K = 0) ∧ reducedDensityFirst m hm (graphState U) a b =
      ((5 : ℂ) ^ (n / 2))⁻¹ ^ 2 * χ K *
        (if coeff hm (U + Uᵀ) (toZ a - toZ b) = 0 then (5 : ℂ) ^ (n - m) else 0) := by sorry
