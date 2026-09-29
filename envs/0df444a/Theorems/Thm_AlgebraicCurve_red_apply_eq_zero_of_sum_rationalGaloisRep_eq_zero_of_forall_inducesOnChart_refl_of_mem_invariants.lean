-- Prove2me | Theorems.Thm_AlgebraicCurve_red_apply_eq_zero_of_sum_rationalGaloisRep_eq_zero_of_forall_inducesOnChart_refl_of_mem_invariants
-- name    : AlgebraicCurve.red_apply_eq_zero_of_sum_rationalGaloisRep_eq_zero_of_forall_inducesOnChart_refl_of_mem_invariants
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/ef10c910-1a81-5b46-846f-2a0f79979e4d
-- title:
--   Chartwise reduction vanishes on averages of chart-trivial automorphisms
-- statement:
--   Let $L$ be an algebraically closed field, $A\subseteq L$ a valuation subring with residue field $\kappa=\mathrm{ResidueField}(A)$, and $F$ a field extension of $L$; let $n\in\mathbb N$ and for each $i<n$ let $\bar F_i$ be a field extension of $\kappa$ together with a component chart $C_i$ of $F$ along $A$ with reduction field $\bar F_i$ (a valuation subring $\mathcal O_i\subseteq F$, a surjective residue map $\mathcal O_i\to\bar F_i$ with kernel the maximal ideal, a domain $\mathrm{dom}(C_i)$ of places of $F/L$, a finite set of nodes among the places of $\bar F_i/\kappa$, a map $\mathrm{placeMap}$ from places of $F/L$ to places of $\bar F_i/\kappa$, and the compatibility axioms of `ComponentChart`). Assume every place of each $\bar F_i/\kappa$ is rational, i.e. $\kappa$ surjects onto its residue field, and every place in $\mathrm{dom}(C_i)$ is rational. Let $\ell$ be a prime, write $V=\mathbb Q_\ell\otimes_{\mathbb Z_\ell}T_\ell\,\mathrm{Pic}^0(F/L)$ for the rational Tate module of the degree-zero divisor class group, let $V^{\mathrm{inv}}\le V$ be a $\mathbb Q_\ell$-submodule and let $\mathrm{red}:V^{\mathrm{inv}}\to\prod_i\mathbb Q_\ell\otimes_{\mathbb Z_\ell}T_\ell\,\mathrm{Pic}^0(\bar F_i/\kappa)$ be $\mathbb Q_\ell$-linear. Two hypotheses tie $\mathrm{red}$ to divisors: first, whenever $w\in V^{\mathrm{inv}}$ is $1\otimes x$ for an integral Tate vector $x$, $k$ is a level, $D$ is a degree-zero divisor on $F/L$ whose class equals the $k$-th component of $x$, and $D=\sum_i D_i$ with each $D_i$ supported in $\mathrm{dom}(C_i)$ and of degree zero, then for each $i$ there is an integral Tate vector $y$ with $\mathrm{red}(w)_i=1\otimes y$ whose $k$-th component is the class of any degree-zero divisor equal to the pushforward $\mathrm{mapDomain}\,\mathrm{placeMap}(D_i)$; second, for such $w=1\otimes x$ and every level $k$ such a decomposition $D=\sum_iD_i$ representing the $k$-th component of $x$ exists. Fix $i$, a finite non-empty type $T$ and a family $u:T\to\mathrm{SemilinearAut}(L,F)$ of pairs $(\sigma,\tau)$ of ring automorphisms of $F$ and of $L$ compatible with $L\to F$, such that each $u_t$ preserves $V^{\mathrm{inv}}$ under the rational Galois representation on $V$, satisfies $f\in\mathcal O_i\iff u_t\cdot f\in\mathcal O_i$, induces the identity on residues, $\overline{u_t\cdot f}=\bar f$ for $f\in\mathcal O_i$, satisfies $P\in\mathrm{dom}(C_i)\iff u_t\cdot P\in\mathrm{dom}(C_i)$ and $\mathrm{placeMap}(u_t\cdot P)=\mathrm{placeMap}(P)$ for $P\in\mathrm{dom}(C_i)$, and permutes the chart domains in the sense that for each $j$ there is $j'$ with $u_t\cdot P\in\mathrm{dom}(C_{j'})$ for all $P\in\mathrm{dom}(C_j)$. Then for every $v\in V^{\mathrm{inv}}$ with $\sum_{t\in T}\rho(u_t)v=0$ in $V$, one has $\mathrm{red}(v)_i=0$.
--
--   This is the vanishing criterion used in the specialisation of $\ell$-adic Tate modules of Jacobians to the components of a semistable reduction: automorphisms acting trivially on a fixed component chart act trivially on the reduction along that chart, so a vector killed by the sum over such a family has vanishing reduction there. It is the step consumed by the cuspidal-specialisation statements for full-level modular curves, where $T$ is a family of unipotent elements fixing an Igusa-type component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_red_apply_eq_zero_of_sum_rationalGaloisRep_eq_zero_of_forall_inducesOnChart_refl_of_mem_invariants.lean

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

theorem AlgebraicCurve.red_apply_eq_zero_of_sum_rationalGaloisRep_eq_zero_of_forall_inducesOnChart_refl_of_mem_invariants
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
    (i : Fin n) {T : Type} [Fintype T] [Nonempty T] (u : T → SemilinearAut L F)
    (huV : ∀ (t : T) (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)), v ∈ Vinv →
      ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) (u t) v ∈ Vinv)
    (hint : ∀ (t : T) (f : F), f ∈ (C i).integers ↔ u t • f ∈ (C i).integers)
    (hres : ∀ (t : T) (f : F) (hf : f ∈ (C i).integers),
      (C i).residue ⟨u t • f, (hint t f).mp hf⟩ = (C i).residue ⟨f, hf⟩)
    (hdom : ∀ (t : T) (P : Place L F), P ∈ (C i).dom ↔ u t • P ∈ (C i).dom)
    (hplace : ∀ (t : T), ∀ P ∈ (C i).dom, (C i).placeMap (u t • P) = (C i).placeMap P)
    (hperm : ∀ (t : T) (j : Fin n), ∃ j', ∀ P : Place L F, P ∈ (C j).dom → u t • P ∈ (C j').dom)
    (v : ↥Vinv)
    (hsum : ∑ t, ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) (u t)
      (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)) = 0) :
    red v i = 0 := by sorry
