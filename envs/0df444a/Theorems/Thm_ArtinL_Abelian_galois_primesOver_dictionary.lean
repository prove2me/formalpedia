-- Prove2me | Theorems.Thm_ArtinL_Abelian_galois_primesOver_dictionary
-- name    : ArtinL.Abelian.galois_primesOver_dictionary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/021c8588-2f1d-5dcd-b3cf-a369b67f7a3f
-- title:
--   Artin's dictionary for primes above p modulo H
-- statement:
--   Let $F$ be an intermediate field of $\mathbb{Q}$ in $\overline{\mathbb{Q}}$ that is a number field and Galois over $\mathbb{Q}$, write $G = \mathrm{Gal}(F/\mathbb{Q})$, let $H \le G$ be a subgroup with fixed field $K = F^{H}$, let $p$ be a prime number and let $P$ be a maximal ideal of $\mathcal{O}_F$ lying over the ideal $(p) \subseteq \mathbb{Z}$. Four assertions are made, where $x \bullet P$ denotes the pointwise action of $G$ on ideals, $Q \mapsto Q \cap \mathcal{O}_K$ is contraction along $\mathcal{O}_K \to \mathcal{O}_F$, and for a maximal ideal $Q$ of $\mathcal{O}_F$ above $(p)$ one writes $D_Q$ for its stabiliser in $G$, $I_Q$ for its inertia subgroup in $G$ and $\mathrm{Frob}_Q$ for the arithmetic Frobenius of $Q$ over $\mathbb{Z}$. (i) Every $v$ in the height-one spectrum of $\mathcal{O}_K$ whose prime ideal contains $p$ is of the form $(x \bullet P) \cap \mathcal{O}_K$ for some $x \in G$. (ii) For $x, y \in G$ one has $(x \bullet P) \cap \mathcal{O}_K = (y \bullet P) \cap \mathcal{O}_K$ if and only if $y = h x d$ for some $h \in H$ and $d \in D_P$. (iii) For every maximal ideal $Q$ of $\mathcal{O}_F$ over $(p)$ and every height-one $v$ of $\mathcal{O}_K$ with $Q \cap \mathcal{O}_K = v$, the inertia degree $f = f(v \mid p)$ of $v$ over $(p)$ satisfies $f \cdot |H \cap D_Q| \cdot |I_Q| = |D_Q| \cdot |H \cap I_Q|$, and for every natural number $j$ there exists $\sigma \in H$ with $\sigma^{-1}\mathrm{Frob}_Q^{\,j} \in I_Q$ if and only if $f \mid j$. (iv) For every height-one $v$ of $\mathcal{O}_K$ containing $p$, $f(v \mid p) > 0$. Cardinalities are natural-number cardinalities of the subgroups named.
--
--   This collects the standard decomposition theory of primes in a Galois extension in the form of a dictionary between the double cosets $H \backslash G / D_P$ and the places of $K = F^H$ above $p$, together with the residue-degree identity $f(v\mid p) = f(Q \mid p)/f(Q \mid v)$ in product form and the description of which powers of $\mathrm{Frob}_Q$ meet $H$ modulo $I_Q$. It is the combinatorial input to Artin's computation of the Euler factor at $p$ of a character induced from $H$, used by [`ArtinL.Abelian.inv_card_inertia_mul_sum_induced_frob_pow_mul_eq_finsum`](thm.html#ArtinL.Abelian.inv_card_inertia_mul_sum_induced_frob_pow_mul_eq_finsum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_Abelian_galois_primesOver_dictionary.lean

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

theorem ArtinL.Abelian.galois_primesOver_dictionary
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (H : Subgroup (F ≃ₐ[ℚ] F)) {p : ℕ} (hp : p.Prime)
    (P : Ideal (𝓞 F)) [P.IsMaximal] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    (∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)),
        ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField H)) ∈ v.asIdeal →
          ∃ x : F ≃ₐ[ℚ] F, (x • P).under (𝓞 ↥(IntermediateField.fixedField H)) = v.asIdeal) ∧
    (∀ x y : F ≃ₐ[ℚ] F,
        (x • P).under (𝓞 ↥(IntermediateField.fixedField H)) =
            (y • P).under (𝓞 ↥(IntermediateField.fixedField H)) ↔
          ∃ h ∈ H, ∃ d ∈ MulAction.stabilizer (F ≃ₐ[ℚ] F) P, y = h * x * d) ∧
    (∀ (Q : Ideal (𝓞 F)) [Q.IsMaximal] [Q.LiesOver (Ideal.span {(p : ℤ)})]
        (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))),
        Q.under (𝓞 ↥(IntermediateField.fixedField H)) = v.asIdeal →
          (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal *
              Nat.card ↥(H ⊓ MulAction.stabilizer (F ≃ₐ[ℚ] F) Q) * Nat.card ↥(Q.inertia (F ≃ₐ[ℚ] F)) =
            Nat.card ↥(MulAction.stabilizer (F ≃ₐ[ℚ] F) Q) * Nat.card ↥(H ⊓ Q.inertia (F ≃ₐ[ℚ] F)) ∧
          ∀ j : ℕ, (∃ σ : F ≃ₐ[ℚ] F, σ ∈ H ∧ σ⁻¹ * arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ j ∈ Q.inertia (F ≃ₐ[ℚ] F)) ↔
            (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal ∣ j) ∧
    (∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)),
        ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField H)) ∈ v.asIdeal →
          0 < (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal) := by sorry
