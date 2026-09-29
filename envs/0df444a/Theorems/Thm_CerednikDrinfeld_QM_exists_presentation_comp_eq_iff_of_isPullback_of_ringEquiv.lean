-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_presentation_comp_eq_iff_of_isPullback_of_ringEquiv
-- name    : CerednikDrinfeld.QM.exists_presentation_comp_eq_iff_of_isPullback_of_ringEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/bbca6365-09ae-5d36-bb7b-4308eca87605
-- title:
--   Tangent presentations transport along a cartesian square over Spec e
-- statement:
--   Let $e : k \xrightarrow{\sim} k'$ be a ring isomorphism of fields, let $f : X \to \operatorname{Spec} k$ and $f' : X' \to \operatorname{Spec} k'$ be morphisms of schemes carrying relative group laws $L$ and $L'$ (functorial group structures on the sets of $T$-points $\{\varphi : T \to X \mid \varphi \circ f = t\}$, natural in $T \to \operatorname{Spec} k$, resp. over $\operatorname{Spec} k'$), and let $i : X' \to X$ be a morphism such that the square with $i$, $f'$, $f$ and $\operatorname{Spec}(e)$ is cartesian and such that $i$ is multiplicative: for every $t' : T \to \operatorname{Spec} k'$ and all points $P, Q$ of $X'$ over $t'$, the composite of $L'.\mathrm{mul}\,t'\,P\,Q$ with $i$ is the $L$-product, over $t'$ followed by $\operatorname{Spec}(e)$, of $P \circ i$ and $Q \circ i$. Let $V$ be a $k$-vector space with a map $\tau$ from $V$ to the points of $X$ over $\operatorname{Spec} k[\varepsilon] \to \operatorname{Spec} k$ which is injective, has image exactly the tangent vectors (those $P$ whose restriction along $\varepsilon \mapsto 0$ is the unit section $L.\mathrm{one}$ over $\operatorname{Spec} k$), is additive for $L.\mathrm{mul}$, and satisfies $\tau(c\cdot v) = \tau(v) \circ \operatorname{Spec}$ of the scaling $\varepsilon \mapsto c\varepsilon$. Give $V$ the $k'$-module structure obtained through $e^{-1}$. Then there exists $\tau'$ on the same $V$, valued in the points of $X'$ over $\operatorname{Spec} k'[\varepsilon] \to \operatorname{Spec} k'$, which is injective, has image exactly the $L'$-tangent vectors, is additive for $L'.\mathrm{mul}$, is homogeneous for the $k'$-scalings of $\operatorname{Spec} k'[\varepsilon]$, and is compatible with endomorphisms: for all $\varphi : X \to X$ over $f$ and $\varphi' : X' \to X'$ over $f'$ with $\varphi'$ followed by $i$ equal to $i$ followed by $\varphi$, and all $v, w \in V$, one has $\tau(w) = \tau(v)$ followed by $\varphi$ if and only if $\tau'(w) = \tau'(v)$ followed by $\varphi'$.
--
--   This is the base-change statement for tangent spaces at the unit of a relative group law along an isomorphism of ground fields: a linear presentation of the tangent space of $X$ transports, on the same underlying abelian group, to one for the base-changed fibre $X'$, and the transport matches differentials of endomorphisms on the two sides. It is used in the study of tangent-space deformation data for fake elliptic curves over algebraically closed fields of positive characteristic, where a presentation over one field must be compared with one over an isomorphic field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_presentation_comp_eq_iff_of_isPullback_of_ringEquiv.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.exists_presentation_comp_eq_iff_of_isPullback_of_ringEquiv
    {k k' : Type} [Field k] [Field k'] (e : k ≃+* k')
    {X X' : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k'))
    (L : RelativeGroupLaw k f) (L' : RelativeGroupLaw k' f')
    (i : X' ⟶ X) (hi : CategoryTheory.IsPullback i f' f (Spec.map (CommRingCat.ofHom e.toRingHom)))
    (himul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of k')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ i =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom e.toRingHom))
          ⟨P.1 ≫ i, by rw [Category.assoc, hi.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ i, by rw [Category.assoc, hi.w, ← Category.assoc, Q.2]⟩).1)

    (V : Type) [AddCommGroup V] [Module k V]
    (τ : V → SchemeHomOver (tangentBase k (RingHom.id k)) f)
    (hinj : Function.Injective τ)
    (hrange : ∀ P : SchemeHomOver (tangentBase k (RingHom.id k)) f, P ∈ Set.range τ ↔ IsTangentVector L k (RingHom.id k) P)
    (hadd : ∀ v w : V, τ (v + w) = L.mul (tangentBase k (RingHom.id k)) (τ v) (τ w))
    (hsmul : ∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) :
    letI : Module k' V := Module.compHom V (e.symm : k' ≃+* k).toRingHom
    ∃ τ' : V → SchemeHomOver (tangentBase k' (RingHom.id k')) f',
      Function.Injective τ' ∧
      (∀ P : SchemeHomOver (tangentBase k' (RingHom.id k')) f', P ∈ Set.range τ' ↔ IsTangentVector L' k' (RingHom.id k') P) ∧
      (∀ v w : V, τ' (v + w) = L'.mul (tangentBase k' (RingHom.id k')) (τ' v) (τ' w)) ∧
      (∀ (c : k') (v : V), (τ' (c • v)).1 = tangentScale k' c ≫ (τ' v).1) ∧

      (∀ (φ : X ⟶ X) (hφ : φ ≫ f = f) (φ' : X' ⟶ X') (hφ' : φ' ≫ f' = f'),
        φ' ≫ i = i ≫ φ →
        ∀ v w : V, τ w = pushPt φ hφ (τ v) ↔ τ' w = pushPt φ' hφ' (τ' v)) := by sorry
