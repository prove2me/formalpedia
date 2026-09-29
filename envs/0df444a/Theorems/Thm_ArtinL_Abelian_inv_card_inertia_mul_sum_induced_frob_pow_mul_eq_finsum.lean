-- Prove2me | Theorems.Thm_ArtinL_Abelian_inv_card_inertia_mul_sum_induced_frob_pow_mul_eq_finsum
-- name    : ArtinL.Abelian.inv_card_inertia_mul_sum_induced_frob_pow_mul_eq_finsum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/8475c9ae-de30-5e70-94e8-b5f449609e5d
-- title:
--   Averaging an induced character over inertia at p
-- statement:
--   Let $F$ be an intermediate field of $\overline{\mathbb Q}/\mathbb Q$ which is a number field and Galois over $\mathbb Q$, put $G=\mathrm{Gal}(F/\mathbb Q)$, let $H\le G$ be a subgroup, $\chi\colon H\to\mathbb C^{\times}$ a homomorphism, $p$ a prime number, $P$ a maximal ideal of $\mathcal O_F$ lying over the ideal $p\mathbb Z$, and $j$ a positive integer. Write $I=P.\mathrm{inertia}\,G$ for the inertia subgroup of $P$ in $G$, $\varphi=$ `arithFrobAt ℤ (F ≃ₐ[ℚ] F) P` for the arithmetic Frobenius at $P$, and $K=$ `IntermediateField.fixedField H`. The assertion is the equality
--   $$\frac1{|I|}\sum_{\tau\in I}\ \frac1{|H|}\sum_{\substack{x\in G\\ x^{-1}\varphi^{j}\tau x\in H}}\chi\bigl(x^{-1}\varphi^{j}\tau x\bigr)\;=\;\sum_{v}^{\ \mathrm{f}}\;c_v,$$
--   the inner double sum being Frobenius' formula for $\mathrm{Ind}_H^G\chi$ evaluated at $\varphi^{j}\tau$ (terms with $x^{-1}\varphi^{j}\tau x\notin H$ contributing $0$), and the right-hand side a finite sum over all $v$ in the height-one spectrum of $\mathcal O_K$, where $c_v=0$ unless $p\in v$ and $f_v:=$ `inertiaDeg'` of $p\mathbb Z$ at $v$ divides $j$, in which case $c_v=f_v\cdot L_v^{\,j/f_v}$. Here $L_v$ is `localValue` of `ofSubgroup H χ` at $v$: the character $\psi$ of $\mathrm{Gal}(F/K)$ obtained from $\chi$ by identifying $\mathrm{Gal}(F/K)$ with the fixing subgroup of $K$, which is $H$, is evaluated at `artinFrob`$=$ `arithFrobAt` $(\mathcal O_K)\,\mathrm{Gal}(F/K)$ at `primeAbove K F v`, provided $\psi$ is trivial on the inertia group of $v$ in $\mathrm{Gal}(F/K)$, and $L_v=0$ otherwise.
--
--   This is Artin's computation of the induced character on a Frobenius coset, expressing the inertia-average of $\mathrm{Ind}_H^G\chi$ at $\varphi^{j}$ in terms of the local values of $\chi$ at the primes of the fixed field $K=F^H$ above $p$; the right-hand side is the $j$-th logarithmic-derivative coefficient of the $p$-Euler polynomial $\prod_{v\mid p}(1-L_vX^{f_v})$ of $L(s,\chi,F/K)$. It is used by [`ArtinL.eulerFactor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum`](thm.html#ArtinL.eulerFactor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum) to match the Euler factor at $p$ of the induced Artin $L$-function with that of the abelian $L$-function over $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_Abelian_inv_card_inertia_mul_sum_induced_frob_pow_mul_eq_finsum.lean

import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Definitions.Def_ArtinL_Abelian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

open scoped Pointwise Classical
open IsDedekindDomain

theorem ArtinL.Abelian.inv_card_inertia_mul_sum_induced_frob_pow_mul_eq_finsum
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (H : Subgroup (F ≃ₐ[ℚ] F)) (χ : H →* ℂˣ) {p : ℕ} (hp : p.Prime)
    (P : Ideal (𝓞 F)) [P.IsMaximal] [P.LiesOver (Ideal.span {(p : ℤ)})] {j : ℕ} (hj : 0 < j) :
    (Fintype.card ↥(P.inertia (F ≃ₐ[ℚ] F)) : ℂ)⁻¹ *
        ∑ τ : ↥(P.inertia (F ≃ₐ[ℚ] F)), ((Nat.card ↥H : ℂ)⁻¹ *
          ∑ x : F ≃ₐ[ℚ] F,
            if hx : x⁻¹ * (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P ^ j * (τ : F ≃ₐ[ℚ] F)) * x ∈ H then
              ((χ ⟨x⁻¹ * (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P ^ j * (τ : F ≃ₐ[ℚ] F)) * x, hx⟩ : ℂˣ) : ℂ)
            else 0) =
      ∑ᶠ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)),
        if ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField H)) ∈ v.asIdeal ∧
            (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal ∣ j then
          ((Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal : ℂ) *
            ArtinL.Abelian.localValue (ArtinL.Abelian.ofSubgroup H χ) v ^
              (j / (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal)
        else 0 := by sorry
