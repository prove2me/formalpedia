-- Prove2me | Theorems.Thm_AlgebraicCurve_mem_span_smul_sub_of_red_eq_zero_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- name    : AlgebraicCurve.mem_span_smul_sub_of_red_eq_zero_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/714c07fa-f636-5df7-bd3e-739cfe65d97e
-- title:
--   Reduction-killed invariant Tate vectors lie in the monodromy span
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A \subseteq L$ a valuation subring with residue field $\kappa$, and $\pi \in A$ a nonzero element of the maximal ideal such that $A$ has rank one in the sense that for every $x \neq 0$ in $L$ and every $y$ in the maximal ideal some power $y^{N}$ has valuation at most that of $x$. Let $F$ be a field over $L$ which is a one-variable function field in the sense of `IsCurveOver` and essentially of finite type, and let $\bar F_1,\dots,\bar F_n$ be fields over $\kappa$, all of whose places are rational. The geometric data consist of component charts $C_i$ (valuation subrings of $F$ with residue map onto $\bar F_i$, a domain of places of $F$, a finite set of nodes in $\bar F_i$ and a place map), all places in chart domains being rational; two families $An_e, An'_e$ ($e < m$) of annuli over $A$ in $F$ with the same domains and moduli, the product of their parameters being the modulus, each modulus a unit times $\pi^{w_e}$; attachment of $An_e$ to $C_{\mathrm{src}(e)}$ at $x_s(e)$ and of $An'_e$ to $C_{\mathrm{tgt}(e)}$ at $x_t(e)$; each node of each chart being an end of exactly one annulus; the chart and annulus domains partitioning the places of $F$, each place lying in exactly one of them; a disc-fibre guard providing, over each non-node point $Q$ of $\bar F_i$, an integral $T$ whose residue has $\mathrm{ord}_Q$ equal to $1$, which is integral with value in the maximal ideal at every place of the fibre and assumes each value of the maximal ideal at exactly one such place; and the genus identity $g(F) + n = \sum_i g(\bar F_i) + m + 1$. Let $S$ be a set of semilinear automorphisms of $F/L$ whose base automorphisms preserve $A$, fix $\pi$ and induce the identity on $\kappa$, which preserve each chart and annulus domain, fix all parameters $An_e.\mathrm{param}$ and $An'_e.\mathrm{param}$, preserve the chart integers with unchanged residues and commute with the place maps; assume every ring automorphism of $L$ with those three properties over $A$ is the base automorphism of some member of $S$. Let $\ell$ be a prime invertible in $\kappa$, assume some $s \in S$ moves an $\ell$-th root of $\pi$, and assume $\mathrm{RationalTateModule}_\ell(\mathrm{Pic}^0(F/L))$ is finite-dimensional over $\mathbb{Q}_\ell$. Let $\mathrm{red}$ be a $\mathbb{Q}_\ell$-linear map from the $S$-invariants $\bigcap_{s \in S} \ker(\rho_\ell(s) - 1)$ to $\prod_i \mathrm{RationalTateModule}_\ell(\mathrm{Pic}^0(\bar F_i/\kappa))$ satisfying the divisorwise compatibility `hred`: whenever an invariant $v$ is $1 \otimes x$ for $x$ in the integral Tate module, and at level $k$ the class of a degree-zero divisor $D$ represents the $k$-th component of $x$, and $D = \sum_i D_i$ with $D_i$ supported in the domain of $C_i$ and of degree zero, then for each $i$ the vector $\mathrm{red}\,v\,i$ is $1 \otimes y$ for some $y$ whose $k$-th component is the class of any degree-zero divisor on $\bar F_i$ equal to the pushforward of $D_i$ along the place map of $C_i$. Assume each $\bar F_i$ is likewise a one-variable function field over $\kappa$, essentially of finite type, with $\#\mathrm{Pic}^0(\bar F_i/\kappa)[\ell^k] = \ell^{2 g(\bar F_i) k}$ for all $k$, and let $M$ be a semistable model over $A$ for these data together with a descent $D$ of $M$. Then every $S$-invariant $v$ with $\mathrm{red}\,v = 0$ lies in the $\mathbb{Q}_\ell$-span of the set of differences $\rho_\ell(s)w - w$ with $s \in S$ and $w$ in the rational Tate module.
--
--   This is one inclusion of Grothendieck's orthogonality relation for a semistable curve: on the inertia invariants of the $\ell$-adic Tate module of $\mathrm{Pic}^0$, the kernel of reduction to the components of the special fibre is the toric (monodromy) part. It is combined with the converse inclusion to give the equality statement [`AlgebraicCurve.red_eq_zero_iff_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel`](thm.html#AlgebraicCurve.red_eq_zero_iff_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_mem_span_smul_sub_of_red_eq_zero_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.lean

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
    AlgebraicCurve.mem_span_smul_sub_of_red_eq_zero_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
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
    (hcount : ∀ (i : Fin n) (k : ℕ),
      Nat.card (Pic0.torsion (IsLocalRing.ResidueField A) (Fbar i) (ℓ ^ k)) =
        ℓ ^ (2 * genusFF (IsLocalRing.ResidueField A) (Fbar i) * k))
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    :
    ∀ v : ↥(⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1)),
      red v = 0 → (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)) ∈ Submodule.span ℚ_[ℓ] {u | ∃ s ∈ S, ∃ w,
        u = ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s w - w} := by sorry
