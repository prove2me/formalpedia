-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_cartierData_kummer_finiteLevel_of_cartierData_of_divisor_of_semistableModel_of_descent
-- name    : AlgebraicCurve.exists_cartierData_kummer_finiteLevel_of_cartierData_of_divisor_of_semistableModel_of_descent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/99a736b9-91cc-5f3c-bd54-2f5044597d5c
-- title:
--   Descent of Kummer Cartier data to a finite henselian level
-- statement:
--   Let $L$ be an algebraically closed field, $A$ a valuation subring of $L$, and $\pi$ a nonzero element of $\mathfrak m_A$; assume $A$ is of rank one in the sense that for every $x\in L^{\times}$ and every $y\in\mathfrak m_A$ some power $y^{n}$ has valuation at most that of $x$. Let $F/L$ be a field extension which is a curve over $L$ (principal divisors exist, all place residue fields are finite over $L$, and $\Omega_{F/L}$ is free of rank one) and essentially of finite type, let $\iota_V,\iota_E$ be finite, and let $\bar F_i$ ($i\in\iota_V$) be curves over the residue field $k_A$ of $A$, essentially of finite type, all of whose places are rational (i.e. $k_A$ surjects onto the place residue field). One is given component charts $C_i$ — valuation subrings of $F$ with surjective residue map onto $\bar F_i$, a node set, a place map, and the chart axioms — whose domain places are rational, paired annuli $An_e,An'_e$ with source and target vertices, node places $x_s(e),x_t(e)$ and widths $w_e$, together with the chart–annulus axioms `hpair` (the two annuli of an edge share domain and modulus, the modulus is nonzero in $L$, and the product of the two parameters is the modulus), `hw` ($(An_e).\mathrm{modulus}$ is a unit times $\pi^{w_e}$), `hatt` (attachment of $An_e$ to $C_{\mathrm{src}\,e}$ at $x_s(e)$ and of $An'_e$ to $C_{\mathrm{tgt}\,e}$ at $x_t(e)$), `hnodes` (each node of each chart is an end of exactly one edge), `hcover` (each place of $F/L$ lies in exactly one chart domain and no annulus, or in exactly one annulus and no chart domain), `hdisc` (at each non-node place $Q$ of $\bar F_i$ a chart-integral $T$ whose residue has order $1$ at $Q$, is in the maximal ideal at each place over $Q$, and realises each $c\in\mathfrak m_A$ as $P.\mathrm{evalAt}\,T$ for a unique such place) and the genus relation $g(F/L)+\#\iota_V=\sum_i g(\bar F_i/k_A)+\#\iota_E+1$; these are summarised here. Further data: a semistable model $M$ of $F$ over $A$ for these charts and annuli, a descent datum $D$ for $M$, a natural number $k$ invertible in $k_A$, a divisor $G$ on $F/L$, a nonzero $g\in F$ with $\operatorname{ord}_P g=k\,G(P)$ for every place $P$, and Cartier data for $G$: opens $U_a$ ($a\in\mathrm{Fin}\,r$) covering $M.X$ and nonzero $h_a\in F$ with $\operatorname{ord}_P h_a=G(P)$ whenever $M.\mathrm{pt}(P)\in U_a$, overlaps satisfying $h_a=h_b(1+t\rho)$ with $t\in\mathfrak m_A$ and $\rho$ in the local subring of $F$ at $x$ (the image of the stalk under $M.\mathrm{ffEquiv}$), one index $a_0$ whose open consists exactly of the points $M.\mathrm{pt}(P)$ with $G(P)=0$, and each $U_a$ of one of three shapes: that of $U_{a_0}$, or the places over a fixed place $q$ of some $\bar F_i$ in the domain of $C_i$ together with those places with $G(P)=0$ and $\operatorname{ord}_P h_a=0$, or the domain of a fixed annulus $An_{e_0}$ together with the same residual part. Finally, nonzero constants $c_i\in L$ with $c_i\,(g/h_a^{k})$ and its inverse lying in $(C_i).\mathrm{integers}$ whenever $M.\mathrm{gen}(i)\in U_a$ and $v(c_{\mathrm{src}\,e})=v(c_{\mathrm{tgt}\,e})$; and a finite level: an intermediate field $K_1$ of $L/D.K_0$, finite over $D.K_0$, whose valuation ring $A_1:=A\cap K_1$ is noetherian henselian local, local maps $j_1:D.A_0\to A_1$ and $\iota_1:A_1\to A$ with $\iota_1$ injective, $\iota_1\circ j_1=D.\iota$, residue-surjective composite, $\iota_1$ compatible with $K_1\subseteq L$, and $A_1$ a discrete valuation ring when $A\neq L$; an integral scheme $X_1$, proper and flat over $\operatorname{Spec}A_1$ with normal stalks, an isomorphism $e_1:M.X\cong X_1\times_{\operatorname{Spec}A_1}\operatorname{Spec}A$ over $\operatorname{Spec}A$, a subfield $F_1\le F$ containing $D.F_0$ and $K_1\cdot 1$, with $F/F_1$ algebraic, an isomorphism $\varphi_1:F_1\cong k(X_1)$ compatible with $M.\mathrm{ffEquiv}$ through the generic-point stalk map of $e_1$ followed by the first projection, and $g$, all $h_a$ in $F_1$ and all $c_i$ in $K_1$. The conclusion: there are a nonzero $c_0\in L$ with $c_0g\in F_1$, the nonzero element $g_1=\varphi_1(c_0g)$ of $k(X_1)$, an $r_1$, opens $U_1$ covering $X_1$ and nonzero $h_1(a)\in k(X_1)$ such that the residue field of $A_1$ is algebraically closed, $k$ is a unit of $A_1$, $g_1/h_1(a)^{k}$ and $h_1(a)^{k}/g_1$ both lie in the image of the stalk at every $x\in U_1(a)$, on overlaps $h_1(a)=h_1(b)\,(1+\mathrm{baseToFunctionField}(f_1)(t)\,s)$ with $t\in\mathfrak m_{A_1}$ and $s$ in the image of the stalk at $x$, and the global-sections map of the closed-fibre projection $X_1\times_{\operatorname{Spec}A_1}\operatorname{Spec}(A_1/\mathfrak m_{A_1})\to\operatorname{Spec}(A_1/\mathfrak m_{A_1})$ is bijective.
--
--   This transports Cartier data $(U_a,h_a)$ for a divisor $G$ with $\operatorname{ord}g=kG$ from the semistable model of $F/L$ over the (possibly non-noetherian) valuation ring $A$ down to a model $X_1$ over a noetherian henselian base $A_1$ at a finite level of the descent datum, and records exactly the hypotheses needed to build a Kummer covering of degree $k$ there. It is used by [`AlgebraicCurve.sum_mem_principal_of_zsmul_mem_principal_of_isNodalPrincipal_mapDomain_placeMap_of_semistableModel_of_descent`](thm.html#AlgebraicCurve.sum_mem_principal_of_zsmul_mem_principal_of_isNodalPrincipal_mapDomain_placeMap_of_semistableModel_of_descent), in the study of reduction on prime-to-$p$ torsion of the divisor class group of a curve with semistable reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_cartierData_kummer_finiteLevel_of_cartierData_of_divisor_of_semistableModel_of_descent.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u

theorem AlgebraicCurve.exists_cartierData_kummer_finiteLevel_of_cartierData_of_divisor_of_semistableModel_of_descent
    {L : Type u} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F]
    {ιV ιE : Type*} [Fintype ιV] [Fintype ιE] (Fbar : ιV → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : ιE → Annulus A F) (src tgt : ιE → ιV)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : ιE → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : ιE ⊕ ιE,
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
    (hgenus : genusFF L F + Fintype.card ιV =
      (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + Fintype.card ιE + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    (k : ℕ) (hk : IsUnit ((k : ℕ) : IsLocalRing.ResidueField A))
    (G : Divisor L F)
    (g : F) (hg : g ≠ 0)
    (hkG : ∀ P : Place L F, P.ord g = (k : ℤ) *
      G P)

    (r : ℕ) (U : Fin r → M.X.Opens) (h : Fin r → F)
    (hU : (⨆ a, U a) = ⊤) (hh : ∀ a, h a ≠ 0)
    (hdiv : ∀ a (P : Place L F), M.pt P ∈ U a → P.ord (h a) =
        G P)
    (hcoc : ∀ a b (x : M.X), x ∈ U a → x ∈ U b →
        ∃ t ∈ IsLocalRing.maximalIdeal A, ∃ r ∈ SemistableModel.localRing M.X M.ffEquiv x,
          h a = h b * (1 + algebraMap L F ((t : A) : L) * r))
    (hv1 : ∃ a₀, ∀ P : Place L F, M.pt P ∈ U a₀ ↔
        G P = 0)
    (hv2 : ∀ a, (∀ P : Place L F, M.pt P ∈ U a ↔
          G P = 0) ∨
        (∃ (i : ιV) (q : Place (IsLocalRing.ResidueField A) (Fbar i)), ∀ P : Place L F,
          M.pt P ∈ U a ↔ ((P ∈ (C i).dom ∧ (C i).placeMap P = q) ∨
            (G P = 0 ∧ P.ord (h a) = 0))) ∨
        (∃ e₀ : ιE, ∀ P : Place L F,
          M.pt P ∈ U a ↔ (P ∈ (An e₀).dom ∨
            (G P = 0 ∧ P.ord (h a) = 0))))

    (c : ιV → L) (hc0 : ∀ i, c i ≠ 0)
    (hcunit : ∀ i a, M.gen i ∈ U a →
        c i • (g / h a ^ k) ∈ (C i).integers ∧ (c i • (g / h a ^ k))⁻¹ ∈ (C i).integers)
    (hcslope : ∀ e', A.valuation (c (src e')) = A.valuation (c (tgt e')))

    (K₁ : IntermediateField ↥D.K₀ L) [FiniteDimensional ↥D.K₀ ↥K₁]
    [IsNoetherianRing ↥(A.comap (algebraMap ↥K₁ L))] [HenselianLocalRing ↥(A.comap (algebraMap ↥K₁ L))]
    (j₁ : D.A₀ →+* ↥(A.comap (algebraMap ↥K₁ L))) (ι₁ : ↥(A.comap (algebraMap ↥K₁ L)) →+* A) [IsLocalHom j₁] [IsLocalHom ι₁]
    (hι₁ : Function.Injective ι₁) (hcomp : ι₁.comp j₁ = D.ι)
    (hres₁ : Function.Surjective ((IsLocalRing.residue A).comp ι₁))
    (hι₁val : ∀ x : ↥(A.comap (algebraMap ↥K₁ L)), ((ι₁ x : A) : L) = algebraMap ↥K₁ L (x : ↥K₁))
    (hdvr : A ≠ ⊤ → IsDiscreteValuationRing ↥(A.comap (algebraMap ↥K₁ L)))

    (X₁ : Scheme.{u}) [IsIntegral X₁] (f₁ : X₁ ⟶ Spec (CommRingCat.of ↥(A.comap (algebraMap ↥K₁ L)))) [IsProper f₁] [Flat f₁]
    (e₁ : M.X ≅ pullback f₁ (Spec.map (CommRingCat.ofHom ι₁)))
    (he₁ : e₁.hom ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁)) = M.toBase)
    (hnorm₁ : ∀ x : X₁, IsIntegrallyClosed (X₁.presheaf.stalk x))
    (F₁ : Subfield F) (φ₁ : F₁ ≃+* X₁.functionField)
    (hF₀ : D.F₀ ≤ F₁) (hK₁ : ∀ x : L, x ∈ K₁ → algebraMap L F x ∈ F₁) (halg : Algebra.IsAlgebraic F₁ F)
    (hcompat : ∃ hgen : (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base (genericPoint M.X) =
        genericPoint X₁,
      ∀ s : F₁, M.ffEquiv (s : F) =
        ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap (genericPoint M.X)).hom
          ((X₁.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom (φ₁ s)))

    (hgF₁ : g ∈ F₁) (hhF₁ : ∀ a, h a ∈ F₁) (hcK₁ : ∀ i, c i ∈ K₁) :
    ∃ (c₀ : L) (hc₀F₁ : c₀ • g ∈ F₁) (g₁ : X₁.functionField)
      (r₁ : ℕ) (U₁ : Fin r₁ → X₁.Opens) (h₁ : Fin r₁ → X₁.functionField),
      c₀ ≠ 0 ∧ g₁ = φ₁ ⟨c₀ • g, hc₀F₁⟩ ∧ g₁ ≠ 0 ∧
      IsAlgClosed (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥K₁ L))) ∧ IsUnit ((k : ℕ) : ↥(A.comap (algebraMap ↥K₁ L))) ∧
      (⨆ a, U₁ a) = ⊤ ∧ (∀ a, h₁ a ≠ 0) ∧
      (∀ a (x : X₁), x ∈ U₁ a →
        g₁ / h₁ a ^ k ∈ (algebraMap (X₁.presheaf.stalk x) X₁.functionField).range ∧
        h₁ a ^ k / g₁ ∈ (algebraMap (X₁.presheaf.stalk x) X₁.functionField).range) ∧
      (∀ a b (x : X₁), x ∈ U₁ a → x ∈ U₁ b →
        ∃ t ∈ IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥K₁ L)), ∃ s ∈ (algebraMap (X₁.presheaf.stalk x) X₁.functionField).range,
          h₁ a = h₁ b * (1 + AlgebraicCurve.SemistableModel.baseToFunctionField f₁ t * s)) ∧
      Function.Bijective
        (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥(A.comap (algebraMap ↥K₁ L)))))).appTop := by sorry
