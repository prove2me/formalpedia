-- Prove2me | Theorems.Thm_DedekindZeta_orbitIdeal_fibre_aux
-- name    : DedekindZeta.orbitIdeal_fibre_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:46:04.99506+00:00
-- url     : https://prove2.me/theorems/94d68a23-cfa3-45b9-8ccf-ab376b466fe9
-- title:
--   Dedekind Zeta: orbit Ideal fibre aux
-- statement:
--   **Bounded-fibre injection for the orbit-indexed principal-ideal map.** With
--   `bfun` a choice of clear-denominator representatives `(bfun a : K) = (d:K)·a` and
--   `ψ o = (bfun (out o))`, each fibre `{o // ψ o = J}` injects into the finite
--   torsion group `torsion K`: two orbit representatives generating the same
--   principal ideal differ by a unit `u = ζ · coneUnitHom g` (Dirichlet,
--   `exist_unique_eq_mul_prod`); the free part `coneUnitHom g` keeps them in the same
--   orbit, so the residual torsion factor `ζ` determines the orbit. Hence the fibre
--   is finite with cardinality `≤ w_K = torsionOrder K`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L2174-L2261
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L2174-L2261

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped NNReal ENNReal

theorem DedekindZeta.orbitIdeal_fibre_aux (I : FractionalIdeal (𝓞 K)⁰ K)
    (bfun : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} → 𝓞 K)
    (hbfun : ∀ a, (bfun a : K) = ((I.den : 𝓞 K) : K) * a.1)
    (hd_ne : ((I.den : 𝓞 K) : K) ≠ 0)
    (ψ : Quotient (MulAction.orbitRel
          (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
          {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}) → NonzeroIdeal K)
    (hψval : ∀ o, ((ψ o : NonzeroIdeal K) : Ideal (𝓞 K))
        = Ideal.span {bfun (Quotient.out o)})
    (J : NonzeroIdeal K) :
    Finite {o // ψ o = J}
      ∧ Nat.card {o // ψ o = J} ≤ NumberField.Units.torsionOrder K := by sorry
