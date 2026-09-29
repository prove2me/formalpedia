-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_ne_zero_ord_eq_of_forall_eq_zero_of_semistableCovering_of_discFibres_of_rankOne
-- name    : AlgebraicCurve.exists_ne_zero_ord_eq_of_forall_eq_zero_of_semistableCovering_of_discFibres_of_rankOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/db5183db-e627-5f03-be98-ecd41abe7770
-- title:
--   Lifting annulus divisors of vanishing interior multidegree
-- statement:
--   Let $L$ be an algebraically closed field, $A\subseteq L$ a valuation subring, and $\pi\in A$ a nonzero element of the maximal ideal; assume the rank-one condition `hrk`: for every $x\in L^{\times}$ and every $y$ in the maximal ideal of $A$ there is $N$ with $A.\mathrm{valuation}(y^{N})\le A.\mathrm{valuation}(x)$. Let $F$ be a field extension of $L$, let $n,m$ be natural numbers and $\bar F_i$ ($i\in\mathrm{Fin}\,n$) fields over the residue field $\kappa_A$ of $A$, all of whose places are rational (the structure map to the residue field of the place is surjective). For each $i$ let $C_i$ be a `ComponentChart A F (Fbar i)`, that is: a valuation subring `integers` of $F$, a surjection `residue` onto $\bar F_i$ with kernel its maximal ideal, a set `dom` of places of $F/L$, a finite set `nodes` of places of $\bar F_i/\kappa_A$, and a reduction map `placeMap` on places, subject to the axioms of that structure; assume every place in $C_i.\mathrm{dom}$ is rational. Let $An_e,An'_e$ ($e\in\mathrm{Fin}\,m$) be `Annulus A F` data (a set `dom` of places, a parameter `param`$\in F$, a `modulus` in the maximal ideal of $A$, with the axioms of that structure), with maps $\mathrm{src},\mathrm{tgt}:\mathrm{Fin}\,m\to\mathrm{Fin}\,n$, places $x^{s}_e$ of $\bar F_{\mathrm{src}(e)}$ and $x^{t}_e$ of $\bar F_{\mathrm{tgt}(e)}$, and widths $w:\mathrm{Fin}\,m\to\mathbb N$, satisfying: $An'_e$ has the same domain and modulus as $An_e$, that modulus is nonzero in $L$, and the product of the two parameters is the image of the modulus (`hpair`); each modulus is a unit times $\pi^{w(e)}$ (`hw`); $An_e$ is attached to $C_{\mathrm{src}(e)}$ at $x^{s}_e$ and $An'_e$ to $C_{\mathrm{tgt}(e)}$ at $x^{t}_e$ in the sense of `IsAttached` (the point is a node, the parameter lies in the chart's integers with residue of order $1$ there, and a unit-comparison property for functions with trivial order on the annulus) (`hatt`); every node of every chart is an end of some annulus, and the map from $\mathrm{Fin}\,m\oplus\mathrm{Fin}\,m$ sending a source end to $(\mathrm{src}(e),x^{s}_e)$ and a target end to $(\mathrm{tgt}(e),x^{t}_e)$ is injective over nodes (`hnodes`); every place of $F/L$ lies either in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain (`hcover`); the disc-fibre condition `hdisc`: for each $i$ and each non-node place $Q$ of $\bar F_i$ there is $T$ in $C_i.\mathrm{integers}$ whose residue is nonzero of order $1$ at $Q$, such that every place $P\in C_i.\mathrm{dom}$ with $\mathrm{placeMap}(P)=Q$ has $T$ in its valuation subring with $P.\mathrm{evalAt}\,T$ in the maximal ideal of $A$, and for every $c$ in the maximal ideal of $A$ there is a unique such $P$ with $P.\mathrm{evalAt}\,T=c$; and the genus identity $\mathrm{genusFF}(L,F)+n=\sum_i\mathrm{genusFF}(\kappa_A,\bar F_i)+m+1$; finally $F/L$ and each $\bar F_i/\kappa_A$ are curves (`IsCurveOver`) and essentially of finite type. Put $V=\mathrm{Fin}\,n\oplus\bigl(\Sigma_e\,\mathrm{Fin}(w(e)-1)\bigr)$, with the edge set $\Sigma_e\,\mathrm{Fin}(w(e))$ whose endpoint map `ends` joins consecutive interior lattice vertices of the $e$-th annulus, the first edge starting at $\mathrm{src}(e)$ and the last ending at $\mathrm{tgt}(e)$; the graph Laplacian `lap` of these data is introduced but does not occur in the conclusion. The assertion is: for every additive map $\mu:\mathrm{Divisor}(L,F)\to(V\to\mathbb Z)$ such that $\mu$ sends a place of $C_i.\mathrm{dom}$ to the indicator of the vertex $i$, sends a place $P$ of $An_e.\mathrm{dom}$ with $P.\mathrm{evalAt}(An_e.\mathrm{param})=u\pi^{d}$ for a unit $u$ and $0<d<w(e)$ to the indicator of the interior vertex $(e,d-1)$, and sends to $0$ a place of $An_e.\mathrm{dom}$ admitting no such expression $u\pi^{d}$; and for every divisor $D_{\mathrm{an}}$ all of whose support lies in annulus domains at such integral depths and with $\mu(D_{\mathrm{an}})$ vanishing at every interior vertex, there exist $f\in F$ nonzero and a divisor $D_f$ with $D_f(P)=P.\mathrm{ord}(f)$ for all places $P$, with $D_f=D_{\mathrm{an}}$ on every annulus domain, and with $\mu(D_f)$ vanishing at every chart vertex $i$.
--
--   This is the lifting step in the theory of semistable coverings of a curve by component charts and annuli: a divisor concentrated at integral depths of the annuli whose multidegree vanishes along the interior lattice vertices of the resolved incidence graph is cut out by a function, up to divisor contributions supported on the chart domains. It is obtained from the corresponding statement formulated via the depth-mass condition, [`AlgebraicCurve.exists_ne_zero_ord_eq_of_depthMass_eq_zero_of_semistableCovering_of_rankOne`](thm.html#AlgebraicCurve.exists_ne_zero_ord_eq_of_depthMass_eq_zero_of_semistableCovering_of_rankOne), and is used in turn by the variant [`AlgebraicCurve.exists_ne_zero_ord_eq_of_sum_eq_zero_of_semistableCovering_of_discFibres_of_rankOne`](thm.html#AlgebraicCurve.exists_ne_zero_ord_eq_of_sum_eq_zero_of_semistableCovering_of_discFibres_of_rankOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_ne_zero_ord_eq_of_forall_eq_zero_of_semistableCovering_of_discFibres_of_rankOne.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_ne_zero_ord_eq_of_forall_eq_zero_of_semistableCovering_of_discFibres_of_rankOne
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)]
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
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    :
    let V := Fin n ⊕ (Σ e : Fin m, Fin (w e - 1))
    let ends : (Σ e : Fin m, Fin (w e)) → V × V := fun ε =>
      (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
       if h1 : ε.2.1 + 1 = w ε.1 then Sum.inl (tgt ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)
    let lap : V → (V → ℤ) := fun v => ∑ ε : Σ e : Fin m, Fin (w e),
      ((if (ends ε).1 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) +
       (if (ends ε).2 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0))
    ∀ μ : Divisor L F →+ (V → ℤ),
      (∀ i, ∀ P ∈ (C i).dom, μ (Finsupp.single P 1) = Pi.single (Sum.inl i) 1) →
      (∀ e, ∀ P ∈ (An e).dom, ∀ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
        (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d → ∀ (hd0 : 0 < d) (hdw : d < w e),
          μ (Finsupp.single P 1) = Pi.single (Sum.inr ⟨e, ⟨d - 1, by omega⟩⟩) 1) →
      (∀ e, ∀ P ∈ (An e).dom,
        (¬ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
          (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) → μ (Finsupp.single P 1) = 0) →
      ∀ Dan : Divisor L F,
        (∀ P ∈ Dan.support, ∃ e, P ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
            (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) →
        (∀ v : Σ e : Fin m, Fin (w e - 1), μ Dan (Sum.inr v) = 0) →
        ∃ (f : F) (Df : Divisor L F), f ≠ 0 ∧ (∀ P, Df P = P.ord f) ∧
          (∀ e, ∀ Q ∈ (An e).dom, Df Q = Dan Q) ∧ ∀ i, μ Df (Sum.inl i) = 0 := by sorry
