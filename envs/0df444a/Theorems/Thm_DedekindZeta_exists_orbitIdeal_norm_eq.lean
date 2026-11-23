-- Prove2me | Theorems.Thm_DedekindZeta_exists_orbitIdeal_norm_eq
-- name    : DedekindZeta.exists_orbitIdeal_norm_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:46:02.855955+00:00
-- url     : https://prove2.me/theorems/7b3a887d-22a8-466c-949c-6d2b4d0d810b
-- title:
--   Dedekind Zeta: exists orbit Ideal norm eq
-- statement:
--   **Orbit-indexed principal-ideal representative with norm identity.** Clearing
--   denominators of `I` via `d := (I.den : 𝓞 K)`, each `G`-orbit `o` of the nonzero
--   elements of `I` has a principal-ideal representative `ψ o = (b₀) ∈ NonzeroIdeal K`
--   with `(b₀ : K) = (d : K)·a₀` (`a₀ = (Quotient.out o).1`), satisfying the norm
--   identity `N(σ a₀)^{-Re t} = N(σ d)^{Re t} · 𝔑(ψ o)^{-Re t}`. The map `ψ` is
--   finite-to-one with each fibre of cardinality `≤ w_K = Units.torsionOrder K`
--   (two reps generating the same principal ideal differ by a unit, hence by a
--   torsion factor modulo the free part `coneUnitHom`; `coneUnitHom_mem_torsion_iff`).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L2271-L2348
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L2271-L2348

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

theorem DedekindZeta.exists_orbitIdeal_norm_eq (I : FractionalIdeal (𝓞 K)⁰ K) {t : ℂ} :
    ∃ ψ : Quotient (MulAction.orbitRel
          (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
          {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}) → NonzeroIdeal K,
      (∀ o, mixedEmbedding.norm (mixedEmbedding K (Quotient.out o).1) ^ (-t.re)
          = mixedEmbedding.norm (mixedEmbedding K ((I.den : 𝓞 K) : K)) ^ t.re
            * (Ideal.absNorm ((ψ o : NonzeroIdeal K) : Ideal (𝓞 K)) : ℝ) ^ (-t.re))
      ∧ (∀ J : NonzeroIdeal K, Finite {o // ψ o = J})
      ∧ (∀ J : NonzeroIdeal K,
          Nat.card {o // ψ o = J} ≤ NumberField.Units.torsionOrder K) := by sorry
