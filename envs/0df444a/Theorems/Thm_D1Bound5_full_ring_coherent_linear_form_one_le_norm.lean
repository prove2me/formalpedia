-- Prove2me | Theorems.Thm_D1Bound5_full_ring_coherent_linear_form_one_le_norm
-- name    : D1Bound5.full_ring_coherent_linear_form_one_le_norm
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:31:29.093163+00:00
-- url     : https://prove2.me/theorems/b67cc6e0-1b64-481f-bb3f-7306fdd90358
-- title:
--   Full ring coherent linear form one le norm
-- statement:
--   For an actual tuple in the FULL integer ring of an imaginary quadratic field, every nonzero polynomial-weighted coherent linear form has complex modulus at least one. Its integrality is derived from the tuple's square witnesses and the analytic branch identities.
-- source:
--   D1Bound5/CoherentIntegralForms.lean, lines 94-129, SHA-256 81e6a044e834ea1f7a20cfce931dfefd9cdd8cbc6a1dc7467c69328d64c38e4c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_IsD1

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5














theorem _root_.D1Bound5.full_ring_coherent_linear_form_one_le_norm
    {K ι : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K] [Fintype ι]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {T : Finset (𝓞 K)} (hT : IsD1 T) {p q : 𝓞 K}
    (hp : p ∈ T) (hq : q ∈ T) (hpq : p ≠ q)
    (a c : ι → 𝓞 K) (Delta : 𝓞 K)
    (ha : ∀ i, a i ∈ T) (hap : ∀ i, a i ≠ p) (haq : ∀ i, a i ≠ q)
    (eta : ℂ) (heta : eta ^ 2 = phi (p : K) * phi (q : K))
    (hL : -phi (Delta : K) * coherentTerminalRoot (phi (p : K)) (phi (q : K)) eta +
      ∑ i, phi (c i : K) *
        coherentAnchorRoot (phi (a i : K)) (phi (p : K)) (phi (q : K)) eta ≠ 0) :
    1 ≤ ‖-phi (Delta : K) * coherentTerminalRoot (phi (p : K)) (phi (q : K)) eta +
      ∑ i, phi (c i : K) *
        coherentAnchorRoot (phi (a i : K)) (phi (p : K)) (phi (q : K)) eta‖ := by sorry

end D1Bound5
end
