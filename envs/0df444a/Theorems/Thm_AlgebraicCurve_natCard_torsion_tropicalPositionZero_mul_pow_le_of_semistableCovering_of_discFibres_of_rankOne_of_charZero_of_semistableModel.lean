-- Prove2me | Theorems.Thm_AlgebraicCurve_natCard_torsion_tropicalPositionZero_mul_pow_le_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
-- name    : AlgebraicCurve.natCard_torsion_tropicalPositionZero_mul_pow_le_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/af3e7f5c-ad66-583d-aa81-5ef788c98584
-- title:
--   Few ℓ^K-torsion classes of tropical position zero
-- statement:
--   Let $L$ be an algebraically closed field of characteristic $0$ and $A \subseteq L$ a valuation subring containing a nonzero element $\pi$ of its maximal ideal and of rank one, in the sense that for every $x \neq 0$ in $L$ and every $y$ in the maximal ideal of $A$ some power $y^{n}$ has valuation at most that of $x$; write $\kappa$ for the residue field of $A$. Let $F$ be a field extension of $L$ which is a curve over $L$ (principal divisors, finite residue extensions, $\Omega_{F/L}$ free of rank one) and essentially of finite type, and let $n, m$ be naturals. The special-fibre data consist of fields $\bar F_i/\kappa$ ($i \in \mathrm{Fin}\,n$), all of whose places over $\kappa$ are rational and which are curves over $\kappa$, essentially of finite type; component charts $C_i$ for $A$, $F$, $\bar F_i$, all places in $(C_i).\mathrm{dom}$ being rational; annuli $\mathrm{An}_e, \mathrm{An}'_e$ ($e \in \mathrm{Fin}\,m$) with source and target indices $\mathrm{src}\,e, \mathrm{tgt}\,e$, node places $x_s(e), x_t(e)$, and widths $w_e$. The hypotheses on these data are: each pair $\mathrm{An}_e, \mathrm{An}'_e$ has the same domain and modulus, that modulus is nonzero in $L$, and the product of the two parameters is the modulus; each modulus is a unit times $\pi^{w_e}$; $\mathrm{An}_e$ is attached to $C_{\mathrm{src}\,e}$ at $x_s(e)$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}\,e}$ at $x_t(e)$; every node of every chart is an edge-end, and is so for exactly one of the $2m$ edge-ends; every place of $F/L$ lies either in exactly one chart domain and no annulus domain, or in exactly one annulus domain and no chart domain; a disc-fibre condition, namely for each $i$ and each non-node place $Q$ of $\bar F_i$ there is $T$ in $(C_i).\mathrm{integers}$ whose residue is nonzero with $\mathrm{ord}_Q = 1$, such that $T$ is regular at every $P \in (C_i).\mathrm{dom}$ over $Q$ with $P$-value in the maximal ideal of $A$, and such that every $c$ in the maximal ideal of $A$ is the value $P.\mathrm{evalAt}\,T$ for a unique such $P$; and the genus identity $g + n = \sum_i g_i + m + 1$, where $g = \mathrm{genusFF}\,L\,F$ and $g_i = \mathrm{genusFF}\,\kappa\,\bar F_i$. Assume further a semistable model $M$ for these data together with a descent $D$ of $M$, a prime $\ell$ whose image in $\kappa$ is a unit, a natural number $K$, an element $\varpi$ of the maximal ideal of $A$ with $\varpi^{\ell^{K}} = \pi$, and that every element $a$ of $\kappa$ satisfies $a^{p^{n}} = a$ for some $n > 0$ whenever $\kappa$ has prime characteristic $p$. Form the vertex set $V = \mathrm{Fin}\,n \sqcup \coprod_e \mathrm{Fin}(\ell^{K} w_e - 1)$ of the $\ell^{K}$-fold subdivision of the dual graph, with edges indexed by pairs $(e, j)$, $j < \ell^{K} w_e$, whose first endpoint is $\mathrm{src}\,e$ if $j = 0$ and the interior vertex $(e, j-1)$ otherwise and whose second endpoint is $\mathrm{tgt}\,e$ if $j + 1 = \ell^{K} w_e$ and $(e, j)$ otherwise, and let $\mathrm{lap}$ be the associated graph Laplacian, $\mathrm{lap}\,v$ being the sum over subdivided edges incident to $v$ of $\delta_v$ minus the indicator of the opposite endpoint. Then for every additive map $\mu : \mathrm{Divisor}\,L\,F \to (V \to \mathbb{Z})$ such that $\mu(\delta_P) = \delta_{i}$ for $P \in (C_i).\mathrm{dom}$, such that $\mu(\delta_P) = \delta_{(e,d-1)}$ whenever $P$ lies in the domain of $\mathrm{An}_e$ and the value of its parameter at $P$ lies in $A$ and equals a unit times $\varpi^{d}$ with $0 < d < \ell^{K} w_e$, and such that $\mu(\delta_P) = 0$ whenever that value admits no expression as a unit times a power of $\varpi$: the set $S$ of classes $c \in \mathrm{Pic}^0(F/L)$ with $\ell^{K} c = 0$ which are represented by a degree-zero divisor $D$ supported in the chart domains and in the $\varpi$-lattice points of the annulus domains and admitting an integral potential $\chi : V \to \mathbb{Z}$ with $\mu(D) = \sum_u \chi(u)\,\mathrm{lap}\,u$ at every vertex is finite, and $\#S \cdot \ell^{K(m+1)} \le \ell^{K(2g+n)}$.
--
--   This is the counting bound for the $\ell^{K}$-torsion of the subgroup of $\mathrm{Pic}^0(F/L)$ cut out by vanishing tropical position, i.e. for the torsion of the identity component of Raynaud's extension attached to a semistable curve over a rank-one valuation ring: equivalently $\#S \le \ell^{K(2\sum_i g_i + b_1)}$ with $b_1 = m + 1 - n$ the cycle rank of the dual graph, obtained by comparison with the nodal Picard group of the special fibre. It is used by the tropical lifting statement [`AlgebraicCurve.exists_pow_zsmul_mk_eq_zero_forall_mu_sub_eq_sum_smul_lap_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel`](thm.html#AlgebraicCurve.exists_pow_zsmul_mk_eq_zero_forall_mu_sub_eq_sum_smul_lap_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_natCard_torsion_tropicalPositionZero_mul_pow_le_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem
    AlgebraicCurve.natCard_torsion_tropicalPositionZero_mul_pow_le_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
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
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : IsLocalRing.ResidueField A)) (K : ℕ)
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    (ϖ : A) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖπ : ϖ ^ (ℓ ^ K) = π)
    (hκ : ∀ p : ℕ, p.Prime → CharP (IsLocalRing.ResidueField A) p →
      ∀ a : IsLocalRing.ResidueField A, ∃ n : ℕ, 0 < n ∧ a ^ (p ^ n) = a)
    :
    let V := Fin n ⊕ (Σ e : Fin m, Fin (ℓ ^ K * w e - 1))
    let ends : (Σ e : Fin m, Fin (ℓ ^ K * w e)) → V × V := fun ε =>
      (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
       if h1 : ε.2.1 + 1 = ℓ ^ K * w ε.1 then Sum.inl (tgt ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)
    let lap : V → (V → ℤ) := fun v => ∑ ε : Σ e : Fin m, Fin (ℓ ^ K * w e),
      ((if (ends ε).1 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) +
       (if (ends ε).2 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0))
    ∀ μ : Divisor L F →+ (V → ℤ),
      (∀ i, ∀ P ∈ (C i).dom, μ (Finsupp.single P 1) = Pi.single (Sum.inl i) 1) →
      (∀ e, ∀ P ∈ (An e).dom, ∀ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
        (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d → ∀ (hd0 : 0 < d) (hdw : d < ℓ ^ K * w e),
          μ (Finsupp.single P 1) = Pi.single (Sum.inr ⟨e, ⟨d - 1, by omega⟩⟩) 1) →
      (∀ e, ∀ P ∈ (An e).dom,
        (¬ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
          (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d) → μ (Finsupp.single P 1) = 0) →
      ∃ hfin : Finite ↥{c : Pic0 L F | ((ℓ ^ K : ℕ) : ℤ) • c = 0 ∧
          ∃ (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)) (χ : V → ℤ),
            Pic0.mk ⟨D, hD⟩ = c ∧
            (∀ P ∈ D.support, (∃ i, P ∈ (C i).dom) ∨
              ∃ e, P ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
                (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d) ∧
            ∀ v : V, μ D v = (∑ u, χ u • lap u) v},
        Nat.card ↥{c : Pic0 L F | ((ℓ ^ K : ℕ) : ℤ) • c = 0 ∧
          ∃ (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)) (χ : V → ℤ),
            Pic0.mk ⟨D, hD⟩ = c ∧
            (∀ P ∈ D.support, (∃ i, P ∈ (C i).dom) ∨
              ∃ e, P ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
                (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d) ∧
            ∀ v : V, μ D v = (∑ u, χ u • lap u) v} * ℓ ^ (K * (m + 1)) ≤
          ℓ ^ (K * (2 * genusFF L F + n)) := by sorry
