-- Prove2me | Theorems.Thm_AlgebraicCurve_add_le_finrank_span_tmul_of_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- name    : AlgebraicCurve.add_le_finrank_span_tmul_of_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/e83df325-9c01-576e-b1c8-b4257c909b1a
-- title:
--   Annulus Tate classes: rank bound m+1≤dimspan+n
-- statement:
--   Let $L$ be an algebraically closed field of characteristic $0$, $A\subseteq L$ a valuation subring, $\pi\in A$ a nonzero element of the maximal ideal, and assume $A$ has rank one in the form: for every $x\in L^{\times}$ and every $y$ in the maximal ideal there is $n$ with $v(y^{n})\le v(x)$. Let $F$ be a field extension of $L$ which is a curve over $L$ (principal divisors exist, residue fields of places are finite over $L$, $\Omega_{F/L}$ free of rank one) and essentially of finite type, and let $\kappa$ be the residue field of $A$. The datum consists of: $n$ fields $\bar F_i/\kappa$, all of whose places are rational, each a curve over $\kappa$ and essentially of finite type; component charts $C_i$ (a valuation subring of $F$ with surjective residue map onto $\bar F_i$ with kernel the maximal ideal, a domain of places of $F/L$, a finite set of nodes among places of $\bar F_i$, and a specialisation map on places), all places in $C_i$'s domain being rational; $m$ pairs of annuli $\mathrm{An}_e,\mathrm{An}'_e$ with the same domain and the same nonzero modulus, the product of their parameters being the modulus, each modulus a unit times $\pi^{w(e)}$, with $\mathrm{An}_e$ attached to $C_{\mathrm{src}(e)}$ at the node $x_s(e)$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}(e)}$ at $x_t(e)$; a combinatorial condition that every node of every chart is an annulus end and is so for exactly one of the $2m$ ends; a covering condition that each place of $F/L$ lies either in exactly one chart domain and no annulus domain, or in exactly one annulus domain and no chart domain; a disc-fibre condition providing, for each non-node place $Q$ of $\bar F_i$, a chart function $T$ with nonzero residue of order $1$ at $Q$, integral at and with value in the maximal ideal at every place above $Q$, such that $T$ parametrises the places above $Q$ bijectively by the maximal ideal of $A$; the genus identity $g(F/L)+n=\sum_i g(\bar F_i/\kappa)+m+1$; a semistable model $M$ for these data over $A$ together with a descent datum $D$ for $M$. Further, $S$ is a set of semilinear automorphisms of $F$ over $L$ (pairs of ring automorphisms compatible with $L\to F$) each of which preserves $A$, fixes $\pi$, acts trivially on $\kappa$, preserves every chart and annulus domain, fixes every parameter of $\mathrm{An}_e$ and $\mathrm{An}'_e$, preserves the chart integers with their residue maps, and commutes with the specialisation maps; and every ring automorphism of $L$ preserving $A$, fixing $\pi$ and trivial on $\kappa$ is the base automorphism of some member of $S$. Let $\ell$ be a prime invertible in $\kappa$, with some member of $S$ moving some $r\in L$ satisfying $r^{\ell}=\pi$, and assume $\mathbb{Q}_{\ell}\otimes_{\mathbb{Z}_{\ell}}T_{\ell}(\mathrm{Pic}^{0}(F/L))$ is finite-dimensional. Let $\xi:\mathbb{N}\to L$ satisfy $\xi_0=1$, $\xi_{k+1}^{\ell}=\xi_k$ and $\xi_1\ne 1$. Finally let $x_e\in T_{\ell}(\mathrm{Pic}^{0}(F/L))$ for $e\in\mathrm{Fin}\,m$ (compatible families with $\ell^{k}x_{e,k}=0$ and $\ell x_{e,k+1}=x_{e,k}$) satisfy: for every $e$, every level $k$ and all places $Q,Q'$ in the domain of $\mathrm{An}_e$ such that some positive power of $Q(z_e)$ is a unit times a power of $\pi$ and $Q'(z_e)=\xi_k\,Q(z_e)$, where $z_e$ is the parameter of $\mathrm{An}_e$, there exist divisors $D_i$ supported in the chart domains with vanishing pushforward along each specialisation map, an integer $r$, annulus indices $e_j$, multiplicities $n_j\in\mathbb{Z}$ and quadruples of places $Q_{j0},\dots,Q_{j3}$ in the domain of $\mathrm{An}_{e_j}$, such that $Q_{j0}(z_{e_j})$ and $Q_{j1}(z_{e_j})$ each have a positive power equal to a unit times a power of $\pi$, $Q_{j0}(z_{e_j})$ is a unit multiple of $Q_{j2}(z_{e_j})$, and $Q_{j0}(z_{e_j})Q_{j1}(z_{e_j})=Q_{j2}(z_{e_j})Q_{j3}(z_{e_j})(1+t)$ with $t$ in the maximal ideal of $A$, and such that whenever the divisor $(Q)-(Q')-\sum_i D_i-\sum_j n_j\big((Q_{j0})+(Q_{j1})-(Q_{j2})-(Q_{j3})\big)$ has degree zero, its class in $\mathrm{Pic}^{0}$ is the $k$-th component of $x_e$. Then $m+1\le \dim_{\mathbb{Q}_{\ell}}\mathrm{span}_{\mathbb{Q}_{\ell}}\{1\otimes x_e : e\in\mathrm{Fin}\,m\}+n$ inside $\mathbb{Q}_{\ell}\otimes_{\mathbb{Z}_{\ell}}T_{\ell}(\mathrm{Pic}^{0}(F/L))$.
--
--   This is the independence statement for the $\ell$-adic classes attached to the annuli of a semistable covering: the classes $1\otimes x_e$ span a subspace of dimension at least $m-n+1$, the cycle rank of the incidence graph of charts and annuli, which is the expected rank of the toric part of the Tate module. It is used in the derivation of the vanishing-cycles statement for semistable coverings, where the relations among the $x_e$ are shown to be exactly the coboundaries coming from the vertices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_add_le_finrank_span_tmul_of_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.lean

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
    AlgebraicCurve.add_le_finrank_span_tmul_of_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
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
    (ξ : ℕ → L) (hξ0 : ξ 0 = 1) (hξ : ∀ k, ξ (k + 1) ^ ℓ = ξ k) (hξ1 : ξ 1 ≠ 1)
    (x : Fin m → TateModule ℓ (Pic0 L F))
    (hx : ∀ e : Fin m,
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
                  - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1), hD⟩)
    :
    m + 1 ≤ Module.finrank ℚ_[ℓ] ↥(Submodule.span ℚ_[ℓ]
      (Set.range fun e : Fin m => ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x e : ModularCurve.RationalTateModule ℓ (Pic0 L F)))) + n := by sorry
