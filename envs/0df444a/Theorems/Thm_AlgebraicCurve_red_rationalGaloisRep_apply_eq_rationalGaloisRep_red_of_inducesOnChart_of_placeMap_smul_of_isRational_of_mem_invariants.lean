-- Prove2me | Theorems.Thm_AlgebraicCurve_red_rationalGaloisRep_apply_eq_rationalGaloisRep_red_of_inducesOnChart_of_placeMap_smul_of_isRational_of_mem_invariants
-- name    : AlgebraicCurve.red_rationalGaloisRep_apply_eq_rationalGaloisRep_red_of_inducesOnChart_of_placeMap_smul_of_isRational_of_mem_invariants
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/0d25a404-11ba-5a89-a6a9-ea4078ccf848
-- title:
--   Naturality of chartwise ℓ-adic reduction under a chart-stabilising automorphism
-- statement:
--   Let $L$ be an algebraically closed field, $A\subseteq L$ a valuation subring with residue field $\kappa=\mathrm{ResidueField}(A)$, and $F$ a field extension of $L$; let $n\in\mathbb N$ and, for $i<n$, let $\bar F_i$ be a field over $\kappa$ together with a chart $C_i : \mathrm{ComponentChart}\,A\,F\,\bar F_i$, that is: a valuation subring $(C_i).\mathrm{integers}$ of $F$ whose intersection with $L$ is $A$, a surjective residue homomorphism onto $\bar F_i$ with kernel the maximal ideal and compatible with the residue map of $A$, a set $(C_i).\mathrm{dom}$ of places of $F/L$, a finite set of nodes among the places of $\bar F_i/\kappa$, and a map $(C_i).\mathrm{placeMap}$ from places of $F$ to places of $\bar F_i$ avoiding the nodes on $(C_i).\mathrm{dom}$, subject to the chart's pointwise-evaluation and divisor push-forward axioms. Assume every place of each $\bar F_i$ over $\kappa$ is rational (the structure map $\kappa\to$ residue field is surjective), and likewise every place of $F$ in $(C_i).\mathrm{dom}$ is rational over $L$. Fix a prime $\ell$, write $T_\ell M$ for the group of sequences $(x_k)$ in $M$ with $\ell^k x_k=0$ and $\ell x_{k+1}=x_k$, and $V=\mathbb Q_\ell\otimes_{\mathbb Z_\ell}T_\ell\,\mathrm{Pic}^0(F/L)$, where $\mathrm{Pic}^0$ is degree-zero divisors modulo principal divisors. Let $V^{\mathrm{inv}}\le V$ be a $\mathbb Q_\ell$-submodule and $\mathrm{red}:V^{\mathrm{inv}}\to\prod_i\mathbb Q_\ell\otimes_{\mathbb Z_\ell}T_\ell\,\mathrm{Pic}^0(\bar F_i/\kappa)$ a $\mathbb Q_\ell$-linear map satisfying two hypotheses: (hred) whenever $v\in V^{\mathrm{inv}}$ equals $1\otimes x$ for an integral Tate vector $x$, and at level $k$ the class of a degree-zero divisor $D$ equals $x_k$, and $D=\sum_i D_i$ with each $D_i$ of degree zero and supported in $(C_i).\mathrm{dom}$, then for each $i$ there is an integral Tate vector $y$ with $\mathrm{red}(v)_i=1\otimes y$ whose level-$k$ component is the class of any degree-zero divisor equal to the push-forward $\mathrm{Finsupp.mapDomain}\,(C_i).\mathrm{placeMap}\,D_i$; and (hrep) for every such $v=1\otimes x$ in $V^{\mathrm{inv}}$ and every level $k$ such a chart-supported decomposition $D=\sum_i D_i$ representing $x_k$ exists. Let $g$ be a semilinear automorphism of $F$ over $L$, i.e. a pair of ring automorphisms of $F$ and of $L$ compatible with the structure map, such that the induced operator $\mathrm{rationalGaloisRep}\,\ell$ at $g$ preserves $V^{\mathrm{inv}}$. Fix $i$ and a $\kappa$-automorphism $\varphi$ of $\bar F_i$ such that $g$ preserves $(C_i).\mathrm{integers}$ in both directions, intertwines the residue map with $\varphi$, preserves $(C_i).\mathrm{dom}$ in both directions, satisfies $(C_i).\mathrm{placeMap}(g\cdot P)=\mathrm{SemilinearAut.ofAlgAut}\,\varphi\cdot (C_i).\mathrm{placeMap}\,P$ for $P\in(C_i).\mathrm{dom}$, and permutes the chart domains in the weak sense that for each $j$ some $j'$ has $g\cdot P\in(C_{j'}).\mathrm{dom}$ for all $P\in(C_j).\mathrm{dom}$. Then for every $v\in V^{\mathrm{inv}}$ the $i$-th component of $\mathrm{red}$ applied to $\mathrm{rationalGaloisRep}\,\ell\,g\,v$ equals $\mathrm{rationalGaloisRep}\,\ell$ at $\varphi$, for the group of $\kappa$-automorphisms of $\bar F_i$ acting on $\mathbb Q_\ell\otimes T_\ell\,\mathrm{Pic}^0(\bar F_i/\kappa)$, applied to $\mathrm{red}(v)_i$.
--
--   This is the equivariance of specialisation of the $\ell$-adic Tate module of a Jacobian along a semistable chart: the chartwise reduction map commutes with the action of a semilinear automorphism of the upper function field and of the $\kappa$-automorphism it induces on the chart's reduced function field. It is used in the vanishing statement [`AlgebraicCurve.red_apply_eq_zero_of_sum_rationalGaloisRep_eq_zero_of_forall_inducesOnChart_refl_of_mem_invariants`](thm.html#AlgebraicCurve.red_apply_eq_zero_of_sum_rationalGaloisRep_eq_zero_of_forall_inducesOnChart_refl_of_mem_invariants) and in the specialisation laws for full-level modular curves, such as [`ModularCurve.FullLevel.exists_algEquiv_inducesOnChart_arithmeticGalois_and_red_eq_of_semistableCovering_of_igusaDom`](thm.html#ModularCurve.FullLevel.exists_algEquiv_inducesOnChart_arithmeticGalois_and_red_eq_of_semistableCovering_of_igusaDom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_red_rationalGaloisRep_apply_eq_rationalGaloisRep_red_of_inducesOnChart_of_placeMap_smul_of_isRational_of_mem_invariants.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open scoped TensorProduct

theorem AlgebraicCurve.red_rationalGaloisRep_apply_eq_rationalGaloisRep_red_of_inducesOnChart_of_placeMap_smul_of_isRational_of_mem_invariants
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (F : Type) [Field F] [Algebra L F]
    (n : ℕ) (Fbar : Fin n → Type) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (C : ∀ i, ComponentChart A F (Fbar i))

    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Vinv : Submodule ℚ_[ℓ] (ModularCurve.RationalTateModule ℓ (Pic0 L F)))
    (red : ↥Vinv →ₗ[ℚ_[ℓ]] ∀ i, ModularCurve.RationalTateModule ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)))
    (hred : ∀ (v : ↥Vinv) (x : TateModule ℓ (Pic0 L F)),
      (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x →
      ∀ (k : ℕ) (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)),
      Pic0.mk ⟨D, hD⟩ = TateModule.proj ℓ (Pic0 L F) k x →
      ∀ Di : Fin n → Divisor L F, D = ∑ i, Di i → (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) →
        (∀ i, Divisor.degree (Di i) = 0) →
        ∀ i, ∃ y : TateModule ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)),
          red v i = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] y ∧
          ∀ E : Divisor.degZero (K := IsLocalRing.ResidueField A) (F := Fbar i),
            (E : Divisor (IsLocalRing.ResidueField A) (Fbar i)) =
                Finsupp.mapDomain (C i).placeMap (Di i) →
              TateModule.proj ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)) k y = Pic0.mk E)

    (hrep : ∀ (v : ↥Vinv) (x : TateModule ℓ (Pic0 L F)),
      (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x →
      ∀ k : ℕ, ∃ (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)) (Di : Fin n → Divisor L F),
        Pic0.mk ⟨D, hD⟩ = TateModule.proj ℓ (Pic0 L F) k x ∧
        D = ∑ i, Di i ∧ (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) ∧ ∀ i, Divisor.degree (Di i) = 0)
    (g : SemilinearAut L F)
    (hgV : ∀ v : ModularCurve.RationalTateModule ℓ (Pic0 L F), v ∈ Vinv →
      ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) g v ∈ Vinv)
    (i : Fin n) (φ : Fbar i ≃ₐ[IsLocalRing.ResidueField A] Fbar i)
    (hint : ∀ f : F, f ∈ (C i).integers ↔ g • f ∈ (C i).integers)
    (hres : ∀ (f : F) (hf : f ∈ (C i).integers), (C i).residue ⟨g • f, (hint f).mp hf⟩ = φ ((C i).residue ⟨f, hf⟩))
    (hdom : ∀ P : Place L F, P ∈ (C i).dom ↔ g • P ∈ (C i).dom)
    (hplace : ∀ P ∈ (C i).dom, (C i).placeMap (g • P) = SemilinearAut.ofAlgAut φ • (C i).placeMap P)
    (hperm : ∀ j, ∃ j', ∀ P : Place L F, P ∈ (C j).dom → g • P ∈ (C j').dom)
    (v : ↥Vinv) :
    red ⟨ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) g v, hgV v v.2⟩ i =
      ModularCurve.rationalGaloisRep ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i))
        (Fbar i ≃ₐ[IsLocalRing.ResidueField A] Fbar i) φ (red v i) := by sorry
