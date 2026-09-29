-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_hom_admissible_of_twoGluedSmoothCurves
-- name    : AlgebraicGeometry.RelPicard.exists_hom_admissible_of_twoGluedSmoothCurves
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/af4a65f3-0e8a-5873-a8bc-b367f71ac6ff
-- title:
--   Admissible gluing data give points of Pic⁰
-- statement:
--   Throughout, $k$ is an algebraically closed field and all schemes live in a fixed universe.
--
--   **Geometric data.** $x : X \to \operatorname{Spec} k$ is proper and $X$ is reduced; $c_1 : C_1 \to \operatorname{Spec} k$ and $c_2 : C_2 \to \operatorname{Spec} k$ are proper, smooth of relative dimension $1$ and geometrically integral. The data $i_1, i_2$ are morphisms $C_1 \to X$, $C_2 \to X$ over $\operatorname{Spec} k$ (elements of `SchemeHomOver c₁ x`, `SchemeHomOver c₂ x`, i.e. morphisms whose composite with $x$ is $c_1$, resp. $c_2$) and both are closed immersions. The hypothesis `hjs` says that every point of $X$ lies in the image of $i_1$ or of $i_2$; `hcr` says that the scheme $C_1 \times_X C_2 =$ `pullback i₁.1 i₂.1` is reduced; a natural number $s$ is given with `hs` stating that the underlying set of $C_1 \times_X C_2$ has cardinality $s$, and `hs0 : 0 < s`. The hypothesis `hc` records that the two projections of $C_1 \times_X C_2$ induce the same morphism to $\operatorname{Spec} k$, namely `pullback.snd i₁.1 i₂.1 ≫ c₂ = pullback.fst i₁.1 i₂.1 ≫ c₁`.
--
--   **Rigidifying sections and Picard designations.** $\varepsilon$ is a $k$-point of $X$ (a section of $x$), $\varepsilon_1$ a $k$-point of $C_1$ with `hε : ε₁.1 ≫ i₁.1 = ε.1`, and $\varepsilon_2$ a $k$-point of $C_2$ (no compatibility with $\varepsilon$ is imposed on $\varepsilon_2$). Each of $D$, $D_1$, $D_2$ is a `RelativePic0Designation`: a scheme together with a structure morphism to $\operatorname{Spec} k$ (written `·.toBase`) and a section of it. The hypotheses $h_D$, $h_{D_1}$, $h_{D_2}$ assert that $D$, $D_1$, $D_2$ represent the respective functors of rigidified line bundles cut out by `algEquivZeroCut`: for a base $t : T \to \operatorname{Spec} k$, the objects are line bundles $L$ on $C \times_{\operatorname{Spec} k} T$ together with a trivialisation of the pullback of $L$ along the rigidifying section determined by $\varepsilon$ (resp. $\varepsilon_1$, $\varepsilon_2$), and the condition `FibrewiseAlgEquivZero` requires that for every algebraically closed field $k'$ and every $k'$-point $s$ of $T$ the restriction of $L$ to the corresponding fibre satisfies `IsAlgEquivZero`. Representability comprises a Poincaré bundle on the total space over `D.toBase` satisfying the condition, the universal property that every such rigidified bundle over $t$ is isomorphic to the pullback of the Poincaré bundle along a unique $T$-point of the designation over $\operatorname{Spec} k$, and triviality of the pullback along the zero section. Via `algEquivZeroGroupCut` (the same condition, shown stable under tensor product and inverses) each designation carries the relative group law `RepresentsRelSubPic.relativeGroupLaw`.
--
--   **Restriction morphisms.** $\nu_1$ and $\nu_2$ are morphisms over $\operatorname{Spec} k$ from the base scheme of $D$ to those of $D_1$ and $D_2$. The hypothesis $h_{\nu_1}$ identifies $\nu_1$ with `RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁`, i.e. the classifying map of the pullback of the Poincaré bundle of $D$ along the curve change induced by $i_1$. The hypothesis $h_{\nu_2}$ is stated pointwise: for every $t : T \to \operatorname{Spec} k$ and every $T$-point $a$ of the base of $D$, the bundle obtained by pulling back the Poincaré bundle of $D_2$ along $a$ followed by $\nu_2$ is isomorphic to the rigidification at $\varepsilon_2$ (in the sense of `Scheme.Modules.rigidify` with the section `rigSection c₂ t ε₂` and the projection `pullback.snd c₂ t`) of the pullback along `curveChange i₂.1 i₂.2 t` of the bundle obtained by pulling back the Poincaré bundle of $D$ along $a$.
--
--   **Function-field data.** $F$ is a field extension of $k$ with `HasPrincipalDivisors k F` and `hCB : ConstantsAreBase k F`, that is $L(0) = \operatorname{im}(k \to F)$. Two curve models $\mathrm{Mdl}_1, \mathrm{Mdl}_2$ of $F$ over $k$ are given together with isomorphisms $e_1 : \mathrm{Mdl}_1.C \cong C_1$, $e_2 : \mathrm{Mdl}_2.C \cong C_2$ compatible with the structure morphisms (`he₁`, `he₂`); each model provides a bijection `pointEquivPlace` between $k$-points of its curve and places of $F/k$.
--
--   **Abel–Jacobi dictionaries of the components.** $\Phi_1$ is a bijection from $\mathrm{Pic}^0(F/k) =$ `Pic0 k F` (degree-zero divisors modulo principal degree-zero divisors) to the $k$-points of the base of $D_1$; `hΦ₁_add` says $\Phi_1$ is additive for the relative group law of $h_{D_1}$, and `hΦ₁` is the pinning: for every $k$-point $P$ of $C_1$ and every degree-zero divisor $Dv$ equal to $[\text{place of } P] - [\text{place of } \varepsilon_1]$ (places computed through $e_1^{-1}$ and `Mdl₁.pointEquivPlace`), the pullback of the Poincaré bundle of $D_1$ along $\Phi_1([Dv])$ is isomorphic to `(RelEffCartierDiv.ofPoint c₁ P.1 P.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₁ ε₁.1 ε₁.2).idealModule`, that is to $\mathcal O(P) \otimes \mathcal O(-\varepsilon_1)$, the first factor being the dual of the ideal sheaf of the graph of $P$ and the second the ideal sheaf of the graph of $\varepsilon_1$. The data $\Phi_2$, `hΦ₂_add`, `hΦ₂` are the same for $c_2$ and $\varepsilon_2$.
--
--   **Enumeration of the crossings.** $S$ is a finite set of pairs of places of $F/k$, $nd$ is a bijection from $S$ to the $k$-points of $C_1 \times_X C_2$ (sections of `pullback.fst i₁.1 i₂.1 ≫ c₁`), and `hS` says that for each $\sigma \in S$ the first member of $\sigma$ is the place of the $C_1$-point obtained from $nd\,\sigma$ by the first projection (read through $e_1^{-1}$) and the second member is the place of the $C_2$-point obtained by the second projection (read through $e_2^{-1}$).
--
--   **Conclusion.** There exists a map $\varphi$ from the group `GluingData.admissible S` — triples $(D_1', D_2', w)$ consisting of two divisors of $F/k$ and a function $S \to \mathrm{Additive}\,k^\times$, subject to: both divisors have degree zero and for each $s \in S$ the first divisor vanishes at $s_1$ and the second at $s_2$ — to the $k$-points of the base of $D$, such that all of the following hold.
--
--   1.
--
--   $\varphi$ is additive: $\varphi(a+b)$ is the product of $\varphi(a)$ and $\varphi(b)$ for the relative group law attached to $h_D$ and `algEquivZeroGroupCut x ε`.
--
--   2.
--
--   If an admissible $a$ satisfies `GluingData.IsGluedPrincipal S a` — there are nonzero $g_1, g_2 \in F$ and $a_\bullet, b_\bullet : S \to k^\times$ such that the first divisor of $a$ is $\operatorname{div} g_1$, the second is $\operatorname{div} g_2$, at each $\sigma \in S$ the function $g_1$ has value $a_\sigma$ at the first place of $\sigma$ and $g_2$ has value $b_\sigma$ at the second place of $\sigma$ (each lying in the valuation ring with prescribed residue), and the unit component of $a$ is $\sigma \mapsto a_\sigma / b_\sigma$ — then $\varphi(a)$ is the identity element of that group law.
--
--   3.
--
--   For every admissible $a$ with components $(D_1', D_2', w)$: the composite of $\varphi(a)$ with $\nu_1$ equals $\Phi_1$ of the class of $D_1'$, and the composite of $\varphi(a)$ with $\nu_2$ equals $\Phi_2$ of the class of $D_2'$ (in each case the class is formed using the degree-zero clauses of admissibility).
--
--   4.
--
--   For every $w : S \to \mathrm{Additive}\,k^\times$, the bundle obtained by pulling back the Poincaré bundle of $D$ along $\varphi(0,0,w)$ satisfies `IsNodeUnitModule` for $x$, $i_1$, $i_2$, the families of $k$-points $\sigma \mapsto nd\,\sigma$ composed with the first, resp. second, projection of $C_1 \times_X C_2$, the base $\mathrm{id}_{\operatorname{Spec} k}$, and the units $\sigma \mapsto$ the image of $(\mathrm{toMul}\,w_\sigma)^{-1}$ under the inverse of the canonical isomorphism $\Gamma(\operatorname{Spec} k,\mathcal O) \cong k$; that is, the bundle admits maps to the pushforwards of the structure sheaves of $C_1$ and $C_2$ such that over every open set the resulting pair map is injective with image exactly those pairs of sections that agree at each crossing up to the prescribed unit (`NodeCondition`).
--
--   5.
--
--   For all $k$-points $P, Q$ of $C_1$ whose images in $X$ (the images of the closed point of $\operatorname{Spec} k$ under $P$ followed by $i_1$, resp. $Q$ followed by $i_1$) do not lie in the image of $i_2$, and every admissible $a$ whose first divisor is $[\text{place of } P] - [\text{place of } Q]$, whose second divisor is $0$ and whose unit component is $0$: the pullback of the Poincaré bundle of $D$ along $\varphi(a)$ is isomorphic to `(RelEffCartierDiv.ofPoint x (P.1 ≫ i₁.1) _).lineBundle ⊗ (RelEffCartierDiv.ofPoint x (Q.1 ≫ i₁.1) _).idealModule`, i.e. to $\mathcal O_X(P)\otimes\mathcal O_X(-Q)$ for the images of $P$ and $Q$ in $X$.
--
--   6.
--
--   Symmetrically, for all $k$-points $P, Q$ of $C_2$ whose images in $X$ under $i_2$ avoid the image of $i_1$, and every admissible $a$ whose first divisor is $0$, whose second divisor is $[\text{place of } P] - [\text{place of } Q]$ and whose unit component is $0$: the pullback of the Poincaré bundle of $D$ along $\varphi(a)$ is isomorphic to $\mathcal O_X(P) \otimes \mathcal O_X(-Q)$, formed as `(RelEffCartierDiv.ofPoint x (P.1 ≫ i₂.1) _).lineBundle ⊗ (RelEffCartierDiv.ofPoint x (Q.1 ≫ i₂.1) _).idealModule`.
--
--   This is the construction half of Raynaud's dictionary for the Picard group of a reduced curve that is the union of two smooth proper geometrically integral components meeting in finitely many points: to an admissible triple (two degree-zero divisors, supported away from the crossings, together with gluing units at the crossings) one attaches a point of the rigidified $\mathrm{Pic}^0$ of $X$, compatibly with the group laws, with restriction to the two components, with the node-unit bundles, and with Abel–Jacobi on each component. It is used by [`AlgebraicGeometry.RelPicard.exists_gluedPic0_equiv_of_twoGluedSmoothCurves`](thm.html#AlgebraicGeometry.RelPicard.exists_gluedPic0_equiv_of_twoGluedSmoothCurves), which turns this map into an isomorphism describing $\mathrm{Pic}^0(X)$ in terms of the components and the crossings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_hom_admissible_of_twoGluedSmoothCurves.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.TwoGluedCurves AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.exists_hom_admissible_of_twoGluedSmoothCurves
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)

    (hc : pullback.snd i₁.1 i₂.1 ≫ c₂ = pullback.fst i₁.1 i₂.1 ≫ c₁)
    (ε : SchemeHomOver (𝟙 _) x) (ε₁ : SchemeHomOver (𝟙 _) c₁) (hε : ε₁.1 ≫ i₁.1 = ε.1)
    (ε₂ : SchemeHomOver (𝟙 _) c₂)
    (D : RelativePic0Designation k x) (hD : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
    (D₁ : RelativePic0Designation k c₁) (hD₁ : RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁)
    (D₂ : RelativePic0Designation k c₂) (hD₂ : RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂)
    (ν₁ : SchemeHomOver D.toBase D₁.toBase) (ν₂ : SchemeHomOver D.toBase D₂.toBase)
    (hν₁ : ν₁ = RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁)
    (hν₂ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
        Nonempty ((hD₂.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L)))

    (F : Type u) [Field F] [Algebra k F] [HasPrincipalDivisors k F] (hCB : ConstantsAreBase k F)
    (Mdl₁ : CurveModel k F) (e₁ : Mdl₁.C ≅ C₁) (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
    (Mdl₂ : CurveModel k F) (e₂ : Mdl₂.C ≅ C₂) (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)

    (Φ₁ : Pic0 k F ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₁.toBase)
    (hΦ₁_add : ∀ a b, Φ₁ (a + b) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).mul _ (Φ₁ a) (Φ₁ b))
    (hΦ₁ : ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (Dv : Divisor.degZero (K := k) (F := F)),
      (Dv : Divisor k F) =
        Finsupp.single (Mdl₁.pointEquivPlace ⟨P.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact P.2⟩) 1 -
          Finsupp.single (Mdl₁.pointEquivPlace ⟨ε₁.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact ε₁.2⟩) 1 →
      Nonempty ((hD₁.poincare.pullbackAlong (Φ₁ (Pic0.mk Dv))).L ≅
        (RelEffCartierDiv.ofPoint c₁ P.1 P.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₁ ε₁.1 ε₁.2).idealModule))
    (Φ₂ : Pic0 k F ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₂.toBase)
    (hΦ₂_add : ∀ a b, Φ₂ (a + b) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).mul _ (Φ₂ a) (Φ₂ b))
    (hΦ₂ : ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂) (Dv : Divisor.degZero (K := k) (F := F)),
      (Dv : Divisor k F) =
        Finsupp.single (Mdl₂.pointEquivPlace ⟨P.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact P.2⟩) 1 -
          Finsupp.single (Mdl₂.pointEquivPlace ⟨ε₂.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact ε₂.2⟩) 1 →
      Nonempty ((hD₂.poincare.pullbackAlong (Φ₂ (Pic0.mk Dv))).L ≅
        (RelEffCartierDiv.ofPoint c₂ P.1 P.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₂ ε₂.1 ε₂.2).idealModule))

    (S : Finset (Place k F × Place k F))
    (nd : ↥S ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (pullback.fst i₁.1 i₂.1 ≫ c₁))
    (hS : ∀ σ : ↥S,
        (σ : Place k F × Place k F).1 = Mdl₁.pointEquivPlace ⟨((nd σ).1 ≫ pullback.fst i₁.1 i₂.1) ≫ e₁.inv,
            by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc, Category.assoc]; exact (nd σ).2⟩ ∧
        (σ : Place k F × Place k F).2 = Mdl₂.pointEquivPlace ⟨((nd σ).1 ≫ pullback.snd i₁.1 i₂.1) ≫ e₂.inv,
            by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc, Category.assoc, hc]; exact (nd σ).2⟩) :
    ∃ φ : ↥(GluingData.admissible S) → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase,

      (∀ a b, φ (a + b) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul _ (φ a) (φ b)) ∧

      (∀ a : ↥(GluingData.admissible S), GluingData.IsGluedPrincipal S (a : GluingData k F S) →
        φ a = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).one _) ∧

      (∀ a : ↥(GluingData.admissible S), postComp ν₁ (φ a) = Φ₁ (Pic0.mk ⟨(a : GluingData k F S).1, a.2.1⟩) ∧
        postComp ν₂ (φ a) = Φ₂ (Pic0.mk ⟨(a : GluingData k F S).2.1, a.2.2.1⟩)) ∧

      (∀ w : ↥S → Additive kˣ,
        IsNodeUnitModule x i₁ i₂
          (fun σ => ⟨(nd σ).1 ≫ pullback.fst i₁.1 i₂.1, by rw [Category.assoc]; exact (nd σ).2⟩)
          (fun σ => ⟨(nd σ).1 ≫ pullback.snd i₁.1 i₂.1, by rw [Category.assoc, hc]; exact (nd σ).2⟩)
          (𝟙 (Spec (CommRingCat.of k)))
          (fun σ => Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom (Additive.toMul (w σ))⁻¹)
          (hD.poincare.pullbackAlong (φ ⟨(0, 0, w), GluingData.zero_zero_mem_admissible S w⟩)).L) ∧

      (∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁)
        (_ : (P.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base)
        (_ : (Q.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base)
        (a : ↥(GluingData.admissible S))
        (_ : (a : GluingData k F S).1 =
          Finsupp.single (Mdl₁.pointEquivPlace ⟨P.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact P.2⟩) 1 -
            Finsupp.single (Mdl₁.pointEquivPlace ⟨Q.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact Q.2⟩) 1)
        (_ : (a : GluingData k F S).2.1 = 0) (_ : (a : GluingData k F S).2.2 = 0),
        Nonempty ((hD.poincare.pullbackAlong (φ a)).L ≅
          (RelEffCartierDiv.ofPoint x (P.1 ≫ i₁.1) (by rw [Category.assoc, i₁.2]; exact P.2)).lineBundle ⊗
            (RelEffCartierDiv.ofPoint x (Q.1 ≫ i₁.1) (by rw [Category.assoc, i₁.2]; exact Q.2)).idealModule)) ∧

      (∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
        (_ : (P.1 ≫ i₂.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₁.1.base)
        (_ : (Q.1 ≫ i₂.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₁.1.base)
        (a : ↥(GluingData.admissible S))
        (_ : (a : GluingData k F S).1 = 0)
        (_ : (a : GluingData k F S).2.1 =
          Finsupp.single (Mdl₂.pointEquivPlace ⟨P.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact P.2⟩) 1 -
            Finsupp.single (Mdl₂.pointEquivPlace ⟨Q.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact Q.2⟩) 1)
        (_ : (a : GluingData k F S).2.2 = 0),
        Nonempty ((hD.poincare.pullbackAlong (φ a)).L ≅
          (RelEffCartierDiv.ofPoint x (P.1 ≫ i₂.1) (by rw [Category.assoc, i₂.2]; exact P.2)).lineBundle ⊗
            (RelEffCartierDiv.ofPoint x (Q.1 ≫ i₂.1) (by rw [Category.assoc, i₂.2]; exact Q.2)).idealModule)) := by sorry
