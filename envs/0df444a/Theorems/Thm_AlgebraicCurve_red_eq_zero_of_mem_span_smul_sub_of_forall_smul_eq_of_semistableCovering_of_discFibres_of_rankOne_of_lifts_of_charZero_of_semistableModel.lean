-- Prove2me | Theorems.Thm_AlgebraicCurve_red_eq_zero_of_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- name    : AlgebraicCurve.red_eq_zero_of_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/0a8ea7a1-68b9-5bf3-be98-42796ba5d51d
-- title:
--   Monodromy differences lie in the kernel of chartwise reduction
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A\subseteq L$ a valuation subring with residue field $\kappa$, and $\pi\in A$ a nonzero element of the maximal ideal; assume $A$ has rank one in the sense that for every $x\in L$, $x\neq0$, and every $y$ in the maximal ideal there is $N$ with $v(y^{N})\le v(x)$. Let $F$ be a field extension of $L$ with `IsCurveOver L F` and essentially of finite type, and let $\bar F_i$, $i\in\mathrm{Fin}\,n$, be fields over $\kappa$, all of whose places are rational (the structure map to the residue field of the place is surjective), each `IsCurveOver` $\kappa$ and essentially of finite type. The covering data are: component charts $C_i$ (a valuation subring $(C_i).\mathrm{integers}$ of $F$ with surjective residue map onto $\bar F_i$ with kernel the maximal ideal, a set $(C_i).\mathrm{dom}$ of places of $F$ all of which are assumed rational, a finite set of nodes in $\bar F_i$, and a place map), annuli $An_e, An'_e$ for $e\in\mathrm{Fin}\,m$ with $\mathrm{src},\mathrm{tgt}:\mathrm{Fin}\,m\to\mathrm{Fin}\,n$, node places $x_s(e),x_t(e)$ and widths $w_e$, subject to: $An'_e$ and $An_e$ have the same domain and modulus, the modulus is nonzero in $L$ and equals the product of the two parameters, the modulus of $An_e$ is $u\pi^{w_e}$ with $u\in A^{\times}$, $An_e$ is attached to $C_{\mathrm{src}(e)}$ at $x_s(e)$ and $An'_e$ to $C_{\mathrm{tgt}(e)}$ at $x_t(e)$, every node of every chart is the endpoint of an annulus and of exactly one (uniqueness as an element of $\mathrm{Fin}\,m\oplus\mathrm{Fin}\,m$), and every place of $F$ lies either in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain. Two further guards: the disc-fibre condition, namely for each $i$ and each non-node place $Q$ of $\bar F_i$ there is $T\in (C_i).\mathrm{integers}$ whose residue is nonzero with $\mathrm{ord}_Q=1$, which lies in the valuation ring of every $P\in (C_i).\mathrm{dom}$ above $Q$ with $P(T)$ in the maximal ideal of $A$, and which takes each value $c$ in the maximal ideal at exactly one such $P$; and the genus identity $g(F)+n=\sum_i g(\bar F_i)+m+1$. Let $S$ be a set of semilinear automorphisms of $F$ over $L$ (pairs of ring automorphisms of $F$ and of $L$ compatible with the structure map) such that each $s\in S$ has base automorphism stabilising $A$, fixing $\pi$ and inducing the identity on $\kappa$, preserving every chart domain and annulus domain, fixing each parameter of $An_e$ and $An'_e$, preserving each $(C_i).\mathrm{integers}$ with unchanged residue, and commuting with each place map; assume moreover that every automorphism of $L$ stabilising $A$, fixing $\pi$ and inducing the identity on $\kappa$ is the base automorphism of some $s\in S$. Let $\ell$ be a prime that is a unit in $\kappa$, and assume some $s\in S$ moves an $\ell$-th root $r$ of $\pi$. Assume $V:=\mathbb{Q}_\ell\otimes_{\mathbb{Z}_\ell}T_\ell(\mathrm{Pic}^0(F/L))$ is finite-dimensional, and let $\mathrm{red}$ be a $\mathbb{Q}_\ell$-linear map from the $S$-invariants $\bigcap_{s\in S}\ker(\rho_\ell(s)-1)\subseteq V$ to $\prod_i \mathbb{Q}_\ell\otimes_{\mathbb{Z}_\ell}T_\ell(\mathrm{Pic}^0(\bar F_i/\kappa))$ satisfying the chartwise compatibility `hred`: whenever an invariant $v$ is $1\otimes x$ with $x$ in the integral Tate module, $k\in\mathbb{N}$, $D$ is a degree-zero divisor whose class is the $k$-th component of $x$, and $D=\sum_i D_i$ with $\mathrm{supp}(D_i)\subseteq (C_i).\mathrm{dom}$ and $\deg D_i=0$, then for each $i$ the vector $\mathrm{red}\,v$ at $i$ is $1\otimes y$ for some integral $y$ whose $k$-th component is the class of any degree-zero divisor equal to the push-forward of $D_i$ along the place map. Finally let $M$ be a semistable model of these data over $A$ and $D$ a descent datum for $M$. The conclusion: for every $S$-invariant $v$, if $v$ lies in the $\mathbb{Q}_\ell$-span of $\{\rho_\ell(s)u-u: s\in S,\ u\in V\}$, then $\mathrm{red}\,v=0$.
--
--   This is the easy inclusion in the kernel theorem describing the chartwise reduction of the $\ell$-adic Tate module of the Jacobian of a semistably covered curve: differences $\rho(s)u-u$ are killed by reduction, because reduction is computed on divisor classes supported in the charts and the semilinear automorphisms in $S$ act trivially on the residue data. It is invoked by the corresponding equivalence [`AlgebraicCurve.red_eq_zero_iff_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel`](thm.html#AlgebraicCurve.red_eq_zero_iff_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel), its converse inclusion, and the vanishing-cycles statement for edges with distinct endpoints.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_red_eq_zero_of_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open scoped TensorProduct

theorem
    AlgebraicCurve.red_eq_zero_of_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : Fin m → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + n = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + m + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (S : Set (SemilinearAut L F))
    (hS : ∀ s ∈ S, (∀ a : L, a ∈ A ↔ SemilinearAut.baseAut s a ∈ A) ∧ SemilinearAut.baseAut s (π : L) = (π : L) ∧
      (∀ (a : A) (h : SemilinearAut.baseAut s (a : L) ∈ A),
        IsLocalRing.residue A ⟨SemilinearAut.baseAut s (a : L), h⟩ = IsLocalRing.residue A a) ∧
      (∀ i, ∀ P ∈ (C i).dom, s • P ∈ (C i).dom) ∧ (∀ e, ∀ P ∈ (An e).dom, s • P ∈ (An e).dom) ∧
      (∀ e, s • (An e).param = (An e).param) ∧ (∀ e, s • (An' e).param = (An' e).param) ∧
      (∀ i, ∀ f : F, ∀ hf : f ∈ (C i).integers, ∃ hf' : s • f ∈ (C i).integers,
        (C i).residue ⟨s • f, hf'⟩ = (C i).residue ⟨f, hf⟩) ∧
      (∀ i, ∀ P ∈ (C i).dom, (C i).placeMap (s • P) = (C i).placeMap P))
    (hSlift : ∀ σ : L ≃+* L, (∀ a : L, a ∈ A ↔ σ a ∈ A) → σ (π : L) = (π : L) →
      (∀ (a : A) (h : σ (a : L) ∈ A), IsLocalRing.residue A ⟨σ (a : L), h⟩ = IsLocalRing.residue A a) →
      ∃ s ∈ S, SemilinearAut.baseAut s = σ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : IsLocalRing.ResidueField A))
    (hSℓ : ∃ s ∈ S, ∃ r : L, r ^ ℓ = (π : L) ∧ SemilinearAut.baseAut s r ≠ r)
    [FiniteDimensional ℚ_[ℓ] (ModularCurve.RationalTateModule ℓ (Pic0 L F))]
    (red : ↥(⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1)) →ₗ[ℚ_[ℓ]]
      ∀ i, ModularCurve.RationalTateModule ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)))
    (hred : ∀ (v : ↥(⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1)))
      (x : TateModule ℓ (Pic0 L F)), (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x →
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
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    :
    ∀ v : ↥(⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1)),
      (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)) ∈ Submodule.span ℚ_[ℓ] {u | ∃ s ∈ S, ∃ w,
        u = ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s w - w} →
        red v = 0 := by sorry
