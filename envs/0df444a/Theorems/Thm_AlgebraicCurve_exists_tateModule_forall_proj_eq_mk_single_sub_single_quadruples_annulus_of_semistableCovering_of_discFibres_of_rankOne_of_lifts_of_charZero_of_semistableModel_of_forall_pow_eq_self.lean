-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_tateModule_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel_of_forall_pow_eq_self
-- name    : AlgebraicCurve.exists_tateModule_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel_of_forall_pow_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/0a45ce8b-d7df-5832-a1e4-72bd0fd42bca
-- title:
--   Annulus Tate classes for a semistable covering exist
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A\subseteq L$ a valuation subring with a nonzero element $\pi$ of its maximal ideal and of rank one in the explicit form assumed here (for every $x\neq 0$ in $L$ and every $y$ in the maximal ideal some power $y^{n}$ has valuation at most that of $x$), $\kappa$ its residue field, and $F$ a field over $L$ which is a curve over $L$ (principal divisors exist, residue fields of places are finite over $L$, and $\Omega_{F/L}$ is free of rank one) and essentially of finite type. The covering data, summarised here, consist of: $n$ component charts $C_i$ with reduction fields $\bar F_i/\kappa$, all places of $\bar F_i$ and all places in the domain of $C_i$ being rational; $m$ pairs of annuli $(\mathrm{An}_e,\mathrm{An}'_e)$ with equal domains, equal nonzero modulus, product of the two parameters equal to the modulus, and modulus a unit times $\pi^{w_e}$; attachment of $\mathrm{An}_e$ to $C_{\mathrm{src}\,e}$ at $xs_e$ and of $\mathrm{An}'_e$ to $C_{\mathrm{tgt}\,e}$ at $xt_e$; every node of every chart is an end of an annulus and the $2m$ ends label the nodes injectively; every place of $F/L$ lies in exactly one chart domain and no annulus domain, or in exactly one annulus domain and no chart domain; disc fibres over each non-nodal place $Q$ of $\bar F_i$, given by a chart integer $T$ whose residue has $\mathrm{ord}_Q=1$ and which identifies the fibre of the chart's place map over $Q$ bijectively with the maximal ideal of $A$; and the genus identity $g(F/L)+n=\sum_i g(\bar F_i/\kappa)+m+1$. Further, $S$ is a set of semilinear automorphisms of $F$ over $L$, each member of which preserves $A$, fixes $\pi$, induces the identity on $\kappa$, preserves every chart and annulus domain, fixes every parameter of every $\mathrm{An}_e$ and $\mathrm{An}'_e$, preserves the chart integers with unchanged residues, and leaves the chart place maps invariant; and every ring automorphism of $L$ with the first three of these properties is the base automorphism of some member of $S$. Finally $\ell$ is a prime invertible in $\kappa$, some member of $S$ moves some $\ell$-th root of $\pi$, the space $\mathbb{Q}_\ell\otimes_{\mathbb{Z}_\ell}T_\ell(\mathrm{Pic}^0(F/L))$ is finite-dimensional over $\mathbb{Q}_\ell$, each $\bar F_i$ is a curve over $\kappa$ and essentially of finite type, $M$ is a semistable model of these data over $A$ equipped with a descent datum $D$, the field $\kappa$ satisfies $a^{p^{n}}=a$ for some $n>0$ for every $a$ whenever $\kappa$ has prime characteristic $p$, and $\xi_0=1$, $\xi_{k+1}^{\ell}=\xi_k$, $\xi_1\neq 1$ is a compatible system of $\ell$-power roots of unity in $L$. Then there is a family $x_e\in T_\ell(\mathrm{Pic}^0(F/L))$, $e<m$, that is, of sequences $(x_e(k))_k$ of divisor classes with $\ell^{k}x_e(k)=0$ and $\ell\, x_e(k+1)=x_e(k)$, with the following levelwise description: for every $e$, every $k$ and all places $Q,Q'$ in the domain of $\mathrm{An}_e$ such that some positive power of $Q$ evaluated at the parameter of $\mathrm{An}_e$ equals a unit of $A$ times a power of $\pi$, and such that $Q'$ evaluated at that parameter equals $\xi_k$ times $Q$ evaluated at it, there exist divisors $D_i$ on $F/L$ supported in the domain of $C_i$ and with vanishing push-forward along the place map of $C_i$, an $r$, indices $e_j<m$, integers $n_j$ and quadruples of places $Q_{j,0},\dots,Q_{j,3}$ in the domain of $\mathrm{An}_{e_j}$, such that for each $j$ the values of $Q_{j,0}$ and $Q_{j,1}$ at the parameter of $\mathrm{An}_{e_j}$ each have a positive power equal to a unit times a power of $\pi$, the value of $Q_{j,0}$ is a unit multiple of that of $Q_{j,2}$, and the product of the values of $Q_{j,0}$ and $Q_{j,1}$ equals the product of those of $Q_{j,2}$ and $Q_{j,3}$ times $1+t$ for some $t$ in the maximal ideal of $A$; and such that, whenever the divisor $(Q)-(Q')-\sum_i D_i-\sum_j n_j\bigl((Q_{j,0})+(Q_{j,1})-(Q_{j,2})-(Q_{j,3})\bigr)$ has degree zero, the $k$-th component of $x_e$ is its class in $\mathrm{Pic}^0(F/L)$.
--
--   This is the $\ell$-adic Kummer (monodromy) class attached to each annulus of a semistable covering, produced as an element of the Tate module of $\mathrm{Pic}^0$ together with an explicit description of each of its $\ell$-power levels by divisors supported on the charts and on annulus quadruples; it is the function-field analogue of the period/monodromy classes of the theory of stable reduction and rigid uniformization. It feeds the computation of the vanishing-cycle subspace and the lower bound for the rank of the span of these classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_tateModule_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel_of_forall_pow_eq_self.lean

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
    AlgebraicCurve.exists_tateModule_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel_of_forall_pow_eq_self
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
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    (hκ : ∀ p : ℕ, p.Prime → CharP (IsLocalRing.ResidueField A) p →
      ∀ a : IsLocalRing.ResidueField A, ∃ n : ℕ, 0 < n ∧ a ^ (p ^ n) = a)
    (ξ : ℕ → L) (hξ0 : ξ 0 = 1) (hξ : ∀ k, ξ (k + 1) ^ ℓ = ξ k) (hξ1 : ξ 1 ≠ 1)
    :
    ∃ x : Fin m → TateModule ℓ (Pic0 L F), ∀ e : Fin m,
      ∀ (k : ℕ) (Q Q' : Place L F), Q ∈ (An e).dom → Q' ∈ (An e).dom →
        (∃ (N d : ℕ) (u : Aˣ), 0 < N ∧ (Q.evalAt (An e).param) ^ N = ((u : A) : L) * (π : L) ^ d) →
        Q'.evalAt (An e).param = ξ k * Q.evalAt (An e).param →
        ∃ (Di : Fin n → Divisor L F) (r : ℕ) (eq : Fin r → Fin m) (nq : Fin r → ℤ) (Qq : Fin r → Fin 4 → Place L F),
          (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) ∧
          (∀ i, Finsupp.mapDomain (C i).placeMap (Di i) = 0) ∧
          (∀ j l, Qq j l ∈ (An (eq j)).dom) ∧
          (∀ j, (∃ (N d : ℕ) (u : Aˣ), 0 < N ∧ ((Qq j 0).evalAt (An (eq j)).param) ^ N = ((u : A) : L) * (π : L) ^ d) ∧
            (∃ (N d : ℕ) (u : Aˣ), 0 < N ∧ ((Qq j 1).evalAt (An (eq j)).param) ^ N = ((u : A) : L) * (π : L) ^ d)) ∧
          (∀ j, ∃ u : Aˣ,
            (Qq j 0).evalAt (An (eq j)).param = ((u : A) : L) * (Qq j 2).evalAt (An (eq j)).param) ∧
          (∀ j, ∃ t ∈ IsLocalRing.maximalIdeal A,
            (Qq j 0).evalAt (An (eq j)).param * (Qq j 1).evalAt (An (eq j)).param =
              (Qq j 2).evalAt (An (eq j)).param * (Qq j 3).evalAt (An (eq j)).param * (1 + ((t : A) : L))) ∧
          ∀ hD : (Finsupp.single Q 1 - Finsupp.single Q' 1 - ∑ i, Di i
              - ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1
                  - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1) : Divisor L F) ∈
              Divisor.degZero (K := L) (F := F),
            TateModule.proj ℓ (Pic0 L F) k (x e) = Pic0.mk ⟨Finsupp.single Q 1 - Finsupp.single Q' 1 - ∑ i, Di i
              - ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1
                  - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1), hD⟩ := by sorry
