-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_mem_iInf_ker_red_eq_zero_of_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- name    : AlgebraicCurve.exists_mem_iInf_ker_red_eq_zero_of_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/6e6ebaed-454e-5fc3-8414-da7b1d5e1b8d
-- title:
--   Annulus classes are S-invariant and killed by chartwise reduction
-- statement:
--   Throughout, $L$ is an algebraically closed field of characteristic $0$, $A \subseteq L$ is a valuation subring, $\kappa :=$ `IsLocalRing.ResidueField A` is its residue field, and $F$ is a field extension of $L$ which is a curve over $L$ in the sense of `IsCurveOver` (principal divisors exist, every place has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank $1$ over $F$) and is of essentially finite type over $L$. Places are the objects of `Place L F`: valuation subrings of $F$ containing the image of $L$, proper and principal; for a place $P$ and $f \in F$, $P.\mathrm{evalAt}\,f \in L$ is the element of $L$ whose residue is that of $f$ when $f$ lies in the valuation ring of $P$ (and $0$ otherwise), and $P$ is rational when $L$ surjects onto its residue field. The genus $\mathrm{genusFF}$ of a function field is the $L$-dimension of $H^1(0)$.
--
--   *Valuation data.* An element $\pi \in A$ is given with $\pi$ in the maximal ideal of $A$ (`hπ`) and $\pi \neq 0$ (`hπ0`), together with the rank-one hypothesis `hrk`: for every $x \in L$, $x \neq 0$, and every $y$ in the maximal ideal of $A$ there is $n \in \mathbb{N}$ with $v_A(y^n) \le v_A(x)$.
--
--   *Covering data.* Natural numbers $n, m$ are given, fields $\bar F_i$ ($i \in \mathrm{Fin}\,n$) over $\kappa$, all of whose places are rational (`hratBar`), component charts $C_i :$ `ComponentChart A F (Fbar i)` (each consisting of a valuation subring of integers in $F$, a surjective residue map onto $\bar F_i$ with kernel the maximal ideal, a domain of places of $F/L$, a finite set of nodes among the places of $\bar F_i/\kappa$, and a map $\mathrm{placeMap}$ from places of $F$ to places of $\bar F_i$, subject to the compatibilities recorded in that structure), all places in the chart domains being rational (`hratF`); annuli $\mathrm{An}_e, \mathrm{An}'_e :$ `Annulus A F` for $e \in \mathrm{Fin}\,m$ (each with a domain of places, a parameter in $F$, a modulus in the maximal ideal of $A$ and the axioms of `Annulus`), maps $\mathrm{src}, \mathrm{tgt} : \mathrm{Fin}\,m \to \mathrm{Fin}\,n$, node-valued endpoints $x^{\mathrm{s}}_e$ on $\bar F_{\mathrm{src}\,e}$ and $x^{\mathrm{t}}_e$ on $\bar F_{\mathrm{tgt}\,e}$, and exponents $w : \mathrm{Fin}\,m \to \mathbb{N}$.
--
--   These are subject to: `hpair` — for each $e$, $\mathrm{An}'_e$ and $\mathrm{An}_e$ have the same domain and the same modulus, that modulus is nonzero in $L$, and the product of the two parameters is the image of the modulus under $L \to F$; `hw` — each modulus is a unit of $A$ times $\pi^{w e}$; `hatt` — $\mathrm{An}_e$ is attached to $C_{\mathrm{src}\,e}$ at $x^{\mathrm{s}}_e$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}\,e}$ at $x^{\mathrm{t}}_e$, where attachment means that the point is a node, the annulus parameter lies in the chart integers with chart residue of order $1$ at that point, and for every chart function with nonzero residue which has order $0$ at all places of the annulus, the quotient of its value by the appropriate power of the annulus parameter is a unit of $A$ at every place of the annulus; `hnodes` — every node of every chart is an endpoint of at least one annulus, and the endpoint assignment $\mathrm{Fin}\,m \oplus \mathrm{Fin}\,m \to \Sigma_j\,\mathrm{Place}(\kappa, \bar F_j)$ takes each node as value at most once; `hcover` — every place of $F/L$ lies either in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain; `hdisc` (disc fibres) — for each chart $i$ and each non-node place $Q$ of $\bar F_i$ there is $T$ in the chart integers whose residue is nonzero and has order $1$ at $Q$, such that every place $P$ of the chart domain with $\mathrm{placeMap}\,P = Q$ has $T$ in its valuation ring with $P.\mathrm{evalAt}\,T$ in the maximal ideal of $A$, and such that for every $c$ in the maximal ideal of $A$ there is a unique place $P$ in the chart domain with $\mathrm{placeMap}\,P = Q$ and $P.\mathrm{evalAt}\,T = c$; and `hgenus` — the genus identity $\mathrm{genusFF}(L, F) + n = \sum_i \mathrm{genusFF}(\kappa, \bar F_i) + m + 1$. Each $\bar F_i$ is in addition assumed to be a curve over $\kappa$ of essentially finite type.
--
--   *Semilinear automorphisms.* A set $S$ of elements of `SemilinearAut L F` is given (pairs of a ring automorphism of $F$ and one of $L$ compatible with $L \to F$; the second component is $\mathrm{baseAut}$). The hypothesis `hS` requires of every $s \in S$ nine clauses: the base automorphism preserves membership in $A$, fixes $\pi$, induces the identity on the residue field of $A$, preserves each chart domain and each annulus domain, fixes the parameter of each $\mathrm{An}_e$ and of each $\mathrm{An}'_e$, preserves the chart integers with unchanged chart residue, and commutes with each $\mathrm{placeMap}$. The hypothesis `hSlift` requires conversely that every ring automorphism $\sigma$ of $L$ which preserves $A$, fixes $\pi$ and acts trivially on the residue field of $A$ be the base automorphism of some $s \in S$.
--
--   *The prime $\ell$ and the reduction map.* A prime $\ell$ is given with $\ell$ a unit in $\kappa$ (`hℓ`) and with some $s \in S$ and some $r \in L$ satisfying $r^{\ell} = \pi$ and $\mathrm{baseAut}\,s\,(r) \neq r$ (`hSℓ`); the rational Tate module $V := \mathbb{Q}_\ell \otimes_{\mathbb{Z}_\ell} T_\ell(\mathrm{Pic}^0(L, F))$ is assumed finite-dimensional over $\mathbb{Q}_\ell$, where $T_\ell(M)$ is the group of compatible systems of $\ell$-power torsion elements of $M$ and $\mathrm{Pic}^0$ is the quotient of degree-zero divisors by principal ones. Write $V^S := \bigcap_{s \in S} \ker(\rho(s) - 1)$ for the common fixed space of the rational Galois representation of `SemilinearAut L F` on $V$. A $\mathbb{Q}_\ell$-linear map $\mathrm{red} : V^S \to \prod_i \mathbb{Q}_\ell \otimes_{\mathbb{Z}_\ell} T_\ell(\mathrm{Pic}^0(\kappa, \bar F_i))$ is given, pinned by `hred`: whenever $v \in V^S$ is $1 \otimes x$ for an integral Tate vector $x$, whenever a level $k$, a degree-zero divisor $D$ on $F/L$ with $\mathrm{Pic}^0$-class equal to the $k$-th component of $x$, and a decomposition $D = \sum_i D_i$ with each $D_i$ supported in the domain of $C_i$ and of degree $0$ are given, then for each $i$ there is an integral Tate vector $y$ of $\mathrm{Pic}^0(\kappa, \bar F_i)$ with $\mathrm{red}(v)_i = 1 \otimes y$ whose $k$-th component is the class of any degree-zero divisor on $\bar F_i$ equal to the push-forward $\mathrm{mapDomain}\,\mathrm{placeMap}\,(D_i)$.
--
--   *Model, roots of unity, and the annulus classes.* A semistable model $M$ of the situation (a proper flat integral scheme over $\operatorname{Spec} A$ of locally finite presentation with function field $F$, with prescribed points for the places, the chart generic points, the smooth chart fibres and the annuli, and the compatibilities of `SemistableModel`) and a descent datum $D : M.\mathrm{Descent}$ over a Noetherian Henselian local subring are given, together with $\xi : \mathbb{N} \to L$ satisfying $\xi_0 = 1$, $\xi_{k+1}^{\ell} = \xi_k$ and $\xi_1 \neq 1$, and a family $x : \mathrm{Fin}\,m \to T_\ell(\mathrm{Pic}^0(L, F))$ of integral Tate vectors.
--
--   The hypothesis `hx` expresses that $x$ is described by the annuli in the following sense. For every $e$, every level $k$ and every pair of places $Q, Q'$ in the domain of $\mathrm{An}_e$ such that $(Q.\mathrm{evalAt}\,z_e)^N = u\,\pi^d$ for some $N > 0$, $d \in \mathbb{N}$ and $u \in A^{\times}$ (where $z_e$ is the parameter of $\mathrm{An}_e$) and such that $Q'.\mathrm{evalAt}\,z_e = \xi_k \cdot Q.\mathrm{evalAt}\,z_e$, there exist divisors $D_i$ on $F/L$, an integer $r$, indices $\mathrm{eq} : \mathrm{Fin}\,r \to \mathrm{Fin}\,m$, coefficients $n_q : \mathrm{Fin}\,r \to \mathbb{Z}$ and places $Q_{j,l}$ ($j \in \mathrm{Fin}\,r$, $l \in \mathrm{Fin}\,4$) such that: each $D_i$ is supported in the domain of $C_i$; each push-forward $\mathrm{mapDomain}\,\mathrm{placeMap}\,(D_i)$ vanishes; each $Q_{j,l}$ lies in the domain of $\mathrm{An}_{\mathrm{eq}\,j}$; for each $j$ both $Q_{j,0}$ and $Q_{j,1}$ satisfy the above power-of-$\pi$ condition for the parameter of $\mathrm{An}_{\mathrm{eq}\,j}$; for each $j$ the values of that parameter at $Q_{j,0}$ and $Q_{j,2}$ differ by a unit of $A$; for each $j$ there is $t$ in the maximal ideal of $A$ with the product of the values at $Q_{j,0}$ and $Q_{j,1}$ equal to the product of the values at $Q_{j,2}$ and $Q_{j,3}$ times $1 + t$; and, provided the divisor
--   $$\Delta := \delta_Q - \delta_{Q'} - \sum_i D_i - \sum_j n_q(j)\,\bigl(\delta_{Q_{j,0}} + \delta_{Q_{j,1}} - \delta_{Q_{j,2}} - \delta_{Q_{j,3}}\bigr)$$
--   has degree zero, the $k$-th component of $x_e$ is the $\mathrm{Pic}^0$-class of $\Delta$.
--
--   Under all these hypotheses the conclusion is: for every $e \in \mathrm{Fin}\,m$ there exists $u$ in the common fixed space $V^S$ such that the underlying element of $V$ is $1 \otimes x_e$, and $\mathrm{red}(u) = 0$.
--
--   This is the statement that the classes attached to the annuli of a semistable covering are invariant under the inertia-type semilinear automorphisms in $S$ and lie in the kernel of the chartwise reduction map, i.e. that they belong to the part of $V_\ell(\mathrm{Pic}^0)$ cut out by the vanishing cycles of the semistable model. It feeds the construction of the vanishing-cycle subspace and the lower bound on the dimension of its span.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_mem_iInf_ker_red_eq_zero_of_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.lean

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
    AlgebraicCurve.exists_mem_iInf_ker_red_eq_zero_of_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
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
    ∀ e : Fin m, ∃ u : ↥(⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1)),
      (u : ModularCurve.RationalTateModule ℓ (Pic0 L F)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x e ∧ red u = 0 := by sorry
