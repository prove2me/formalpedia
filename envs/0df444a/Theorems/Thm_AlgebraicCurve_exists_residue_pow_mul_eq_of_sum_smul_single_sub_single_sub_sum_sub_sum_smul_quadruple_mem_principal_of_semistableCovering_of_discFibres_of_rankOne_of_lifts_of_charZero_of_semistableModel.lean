-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_residue_pow_mul_eq_of_sum_smul_single_sub_single_sub_sum_sub_sum_smul_quadruple_mem_principal_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- name    : AlgebraicCurve.exists_residue_pow_mul_eq_of_sum_smul_single_sub_single_sub_sum_sub_sum_smul_quadruple_mem_principal_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/bd2cd15e-2281-52bf-88d2-7a7fee9f9998
-- title:
--   Level-k Kummer relation forces a vertex coboundary
-- statement:
--   Let $L$ be an algebraically closed field of characteristic $0$, $A \subseteq L$ a valuation subring with residue field $\kappa$, and $\pi$ a nonzero element of the maximal ideal of $A$; assume $A$ has rank one in the form: for every nonzero $x \in L$ and every $y$ in the maximal ideal there is $n$ with $A.\mathrm{valuation}(y^n) \le A.\mathrm{valuation}(x)$. Let $F$ be a field extension of $L$ which is a curve over $L$ in the project's sense (principal divisors exist, finite residue extensions, $\Omega_{F/L}$ free of rank one) and essentially of finite type. The combinatorial datum is: fields $\bar F_i$ over $\kappa$ for $i \in \{0,\dots,n-1\}$, all of whose places are rational; component charts $C_i$ (a valuation subring of $F$ with residue map onto $\bar F_i$, a domain of places of $F/L$, a finite set of nodes, and a reduction map on places); annuli $\mathrm{An}_e, \mathrm{An}'_e$ for $e \in \{0,\dots,m-1\}$ with source and target vertices $\mathrm{src}\,e,\ \mathrm{tgt}\,e$ and node places $x_{s}(e), x_{t}(e)$; weights $w_e$. The hypotheses on this datum, summarised here, are: all places in each $(C_i).\mathrm{dom}$ are rational; $\mathrm{An}'_e$ has the same domain and modulus as $\mathrm{An}_e$, the modulus is nonzero in $L$ and the two parameters multiply to it; each modulus is a unit times $\pi^{w_e}$; $\mathrm{An}_e$ is attached to $C_{\mathrm{src}\,e}$ at $x_s(e)$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}\,e}$ at $x_t(e)$; every node of every chart is hit by exactly one annulus end; the chart and annulus domains partition the places of $F/L$; non-node places of each $\bar F_i$ have discoid fibres (a chart function $T$ with nonzero residue of order $1$ at $Q$, whose values at the places above $Q$ lie in the maximal ideal and realise each such value exactly once); and the genus relation $g(F/L) + n = \sum_i g(\bar F_i/\kappa) + m + 1$. Further, $S$ is a set of semilinear automorphisms of $F$ over $L$ (pairs consisting of a ring automorphism of $F$ and one of $L$ compatible with the structure map) each of which preserves $A$, fixes $\pi$, induces the identity on $\kappa$, preserves every chart and annulus domain, fixes all annulus parameters, preserves the chart valuation rings and their residues, and commutes with the reduction maps; every automorphism of $L$ with the first three of these properties is realised by an element of $S$. A prime $\ell$ is invertible in $\kappa$, some $s \in S$ moves an $\ell$-th root $r$ of $\pi$, the $\ell$-adic rational Tate module of $\mathrm{Pic}^0(F/L)$ is finite dimensional over $\mathbb{Q}_\ell$, each $\bar F_i$ is a curve over $\kappa$ essentially of finite type, and there are a semistable model $M$ over $A$ for this covering together with a descent datum $D$. Finally, $\xi : \mathbb{N} \to L$ satisfies $\xi_0 = 1$, $\xi_{k+1}^{\ell} = \xi_k$ and $\xi_1 \ne 1$. Fix a level $k$, integers $c_e$, places $Q_e, Q'_e$ in $(\mathrm{An}_e).\mathrm{dom}$ such that some positive power of the parameter value at $Q_e$ is a unit times a power of $\pi$ and the parameter value at $Q'_e$ equals $\xi_k$ times that at $Q_e$; divisors $D_i$ supported in $(C_i).\mathrm{dom}$ whose push-forward along the reduction map vanishes; and a finite family indexed by $j \in \iota$ of quadruples $Q_{j,0},\dots,Q_{j,3}$ in $(\mathrm{An}_{e_j}).\mathrm{dom}$ with integer weights $n_j$ such that the parameter value at $Q_{j,0}$ is a unit times that at $Q_{j,2}$, and the values satisfy $z(Q_{j,0})z(Q_{j,1}) = z(Q_{j,2})z(Q_{j,3})(1+t_j)$ with $t_j$ in the maximal ideal. Assume that $$\sum_e c_e([Q_e]-[Q'_e]) - \sum_i D_i - \sum_j n_j([Q_{j,0}]+[Q_{j,1}]-[Q_{j,2}]-[Q_{j,3}])$$ is principal, i.e. is the divisor of orders of a nonzero element of $F$. The conclusion is that $\xi_k \in A$ and there are nonzero $b_i \in \kappa$ with $\bar\xi_k^{\,c_e} \, b_{\mathrm{src}\,e} = b_{\mathrm{tgt}\,e}$ for every edge $e$, where $\bar\xi_k$ is the residue of $\xi_k$ and the exponent is an integer power in $\kappa$.
--
--   This is the level-$k$ coboundary law for Kummer classes on a rank-one semistable covering, in the edition allowing balanced annulus quadruples in the relation: any principal relation among the level-$k$ Kummer divisors is a coboundary of a nonvanishing vertex function on the dual graph. It is used in the proof of the lower bound for the dimension of the span of the corresponding Kummer tensors, which is the independence statement for the level-$k$ Kummer classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_residue_pow_mul_eq_of_sum_smul_single_sub_single_sub_sum_sub_sum_smul_quadruple_mem_principal_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem
    AlgebraicCurve.exists_residue_pow_mul_eq_of_sum_smul_single_sub_single_sub_sum_sub_sum_smul_quadruple_mem_principal_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
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
    (k : ℕ) (c : Fin m → ℤ)
    (Q Q' : Fin m → Place L F) (hQ : ∀ e, Q e ∈ (An e).dom) (hQ' : ∀ e, Q' e ∈ (An e).dom)
    (hQrat : ∀ e, ∃ (N d : ℕ) (u : Aˣ), 0 < N ∧ ((Q e).evalAt (An e).param) ^ N = ((u : A) : L) * (π : L) ^ d)
    (hQQ' : ∀ e, (Q' e).evalAt (An e).param = ξ k * (Q e).evalAt (An e).param)
    (Di : Fin n → Divisor L F) (hDi : ∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom)
    (hred : ∀ i, Finsupp.mapDomain (C i).placeMap (Di i) = 0)
    {ι : Type} [Fintype ι] (eq : ι → Fin m) (nq : ι → ℤ) (Qq : ι → Fin 4 → Place L F)
    (hQq : ∀ j l, Qq j l ∈ (An (eq j)).dom)
    (hrad : ∀ j, ∃ u : Aˣ,
      (Qq j 0).evalAt (An (eq j)).param = ((u : A) : L) * (Qq j 2).evalAt (An (eq j)).param)
    (hbal : ∀ j, ∃ t ∈ IsLocalRing.maximalIdeal A,
      (Qq j 0).evalAt (An (eq j)).param * (Qq j 1).evalAt (An (eq j)).param =
        (Qq j 2).evalAt (An (eq j)).param * (Qq j 3).evalAt (An (eq j)).param * (1 + ((t : A) : L)))
    (hprin : (∑ e, c e • ((Finsupp.single (Q e) 1 : Divisor L F) - Finsupp.single (Q' e) 1)) - (∑ i, Di i)
      - (∑ j, nq j • ((Finsupp.single (Qq j 0) 1 : Divisor L F) + Finsupp.single (Qq j 1) 1
          - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1)) ∈
      Divisor.principal (K := L) (F := F))
    :
    ∃ (hξA : ξ k ∈ A) (b : Fin n → IsLocalRing.ResidueField A), (∀ i, b i ≠ 0) ∧
      ∀ e, (IsLocalRing.residue A ⟨ξ k, hξA⟩) ^ (c e) * b (src e) = b (tgt e) := by sorry
