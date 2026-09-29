-- Prove2me | Theorems.Thm_AutomorphicForm_apply_det_heckeGen_add_eq_and_mul_eq_and_cNorm_eq_of_under_eq_of_sigmaInvariant_or_sigmaReversed
-- name    : AutomorphicForm.apply_det_heckeGen_add_eq_and_mul_eq_and_cNorm_eq_of_under_eq_of_sigmaInvariant_or_sigmaReversed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/421ded58-8761-5f22-a39d-7273beb37738
-- title:
--   Fibrewise constancy of symmetric data of an unramified character pair
-- statement:
--   Let $L/K$ be an extension of number fields that is finite and Galois, let $D$ be an idele Galois descent datum for $\mathcal{O}_L$ over $K$ and $L$, that is, a monoid homomorphism $\tau \mapsto D.\mathrm{act}\,\tau$ from $\mathrm{Gal}(L/K)$ to the ring automorphisms of the adele ring of $L$, each continuous and compatible with the algebra map from $L$, and let $\sigma$ be a $K$-automorphism of $L$ such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$. Let $SL$ be a finite set of height-one primes of $\mathcal{O}_L$ which is saturated over $K$: if $w, w'$ have the same image under `HeightOneSpectrum.under (𝓞 K)`, then $w \in SL$ iff $w' \in SL$. Let $\chi_1, \chi_2$ be monoid homomorphisms from the units of the adele ring of $L$ to $\mathbb{C}^\times$ such that for every $w \notin SL$ each $\chi_i$ is unramified at $w$, meaning that its local component (the composite of $\chi_i$ with `localUnit` at $w$ and with the inclusion `finIncl` of the finite adeles into the adeles, on units) is trivial on every unit $t$ of the completion $L_w$ with both $t$ and $t^{-1}$ in the valuation ring. Assume further that the pair is $\sigma$-invariant, $\chi_i(D.\mathrm{unitsAct}\,\sigma\,z) = \chi_i(z)$ for $i = 1,2$ and all adelic units $z$, or $\sigma$-reversed, $\chi_1(D.\mathrm{unitsAct}\,\sigma\,z) = \chi_2(z)$ and $\chi_2(D.\mathrm{unitsAct}\,\sigma\,z) = \chi_1(z)$, where $D.\mathrm{unitsAct}\,\sigma$ is the automorphism of adelic units induced by $D.\mathrm{act}\,\sigma$. Then for any two primes $w, w' \notin SL$ of $\mathcal{O}_L$ with the same prime of $\mathcal{O}_K$ below them, writing $g_w$ for the determinant of the matrix `heckeGen (𝓞 L) L w` in $GL_2$ of the adele ring (obtained by `diagOne` from the adelic unit attached to the chosen uniformiser at $w$), one has $\chi_1(g_w) + \chi_2(g_w) = \chi_1(g_{w'}) + \chi_2(g_{w'})$ and $\chi_1(g_w)\,\chi_2(g_w) = \chi_1(g_{w'})\,\chi_2(g_{w'})$ as complex numbers, and the absolute norms agree, $\mathrm{cNorm}\,w = \mathrm{cNorm}\,w'$, where $\mathrm{cNorm}\,v$ is the absolute norm of the ideal of $v$ viewed in $\mathbb{C}$.
--
--   The statement expresses that the elementary symmetric functions of an unramified pair of idele class characters of a cyclic extension, together with the residue norm, depend only on the prime of the base field below: the data attached to the primes in a fibre of $L/K$ assemble into well-defined base data. It feeds the $\sigma$-twisted continuous-term analysis on the Langlands–Tunnell route, being used in the construction of the limiting Hecke data for $\sigma$-twisted automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_apply_det_heckeGen_add_eq_and_mul_eq_and_cNorm_eq_of_under_eq_of_sigmaInvariant_or_sigmaReversed.lean

import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_ArithCuspRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.AdelicLevel
open scoped Pointwise

theorem AutomorphicForm.apply_det_heckeGen_add_eq_and_mul_eq_and_cNorm_eq_of_under_eq_of_sigmaInvariant_or_sigmaReversed
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (χ₁ χ₂ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hur : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
      NumberField.TateGlobal.IsUnramifiedCharAt χ₁ w ∧ NumberField.TateGlobal.IsUnramifiedCharAt χ₂ w)
    (hrel : (∀ z : (AdeleRing (𝓞 L) L)ˣ, χ₁ (D.unitsAct σ z) = χ₁ z ∧ χ₂ (D.unitsAct σ z) = χ₂ z) ∨
      (∀ z : (AdeleRing (𝓞 L) L)ˣ, χ₁ (D.unitsAct σ z) = χ₂ z ∧ χ₂ (D.unitsAct σ z) = χ₁ z))
    (w w' : HeightOneSpectrum (𝓞 L)) (hw : w ∉ SL) (hw' : w' ∉ SL)
    (h : HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w') :
    ((χ₁ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)) : ℂˣ) : ℂ) +
        ((χ₂ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)) : ℂˣ) : ℂ) =
      ((χ₁ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w')) : ℂˣ) : ℂ) +
        ((χ₂ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w')) : ℂˣ) : ℂ) ∧
    ((χ₁ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)) : ℂˣ) : ℂ) *
        ((χ₂ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)) : ℂˣ) : ℂ) =
      ((χ₁ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w')) : ℂˣ) : ℂ) *
        ((χ₂ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w')) : ℂˣ) : ℂ) ∧
    AutomorphicForm.HeckeEigensystem.cNorm w = AutomorphicForm.HeckeEigensystem.cNorm w' := by sorry
