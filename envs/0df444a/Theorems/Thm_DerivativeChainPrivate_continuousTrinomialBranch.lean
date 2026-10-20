-- Prove2me | Theorems.Thm_DerivativeChainPrivate_continuousTrinomialBranch
-- name    : DerivativeChainPrivate.continuousTrinomialBranch
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-18T07:40:52.25015+00:00
-- url     : https://prove2.me/theorems/2c19b1f5-5b7a-419c-960f-f8b7d83f5258
-- title:
--   Continuous nonsingular root branch for normalized trinomials
-- statement:
--   For positive integers d<e and a real phase 0<psi<pi, there exists a continuous nonzero complex root branch on all positive T for x^(e-d)(x^d-1)=T exp(i psi). Every selected root is nonsingular. No outermost-modulus or chain-length assertion is made.
-- source:
--   Derivative-zero chains: public formalization reference, R41, DerivativeChainPrivate.continuousTrinomialBranch. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Definitions.Def_DerivativeChainPrivate_foundations
open Filter Topology
open scoped BigOperators
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem DerivativeChainPrivate.continuousTrinomialBranch (d e : ℕ) (hd : 0 < d) (hde : d < e)
    (psi : ℝ) (hpsi : 0 < psi) (hpi : psi < Real.pi) :
    ∃ f : Set.Ioi (0 : ℝ) → ℂ, Continuous f ∧ ∀ T,
      f T ^ (e - d) * (f T ^ d - 1) =
        (T : ℂ) * Complex.exp ((psi : ℂ) * Complex.I) ∧
      f T ≠ 0 ∧
      (Polynomial.X ^ e - Polynomial.X ^ (e - d) -
        Polynomial.C ((T : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))).derivative.eval (f T) ≠ 0 := by sorry
