-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_equiv_torsion_and_forall_pushPt_eq_mulVec_of_forall_exists_eq_of_isMaximalOrder
-- name    : CerednikDrinfeld.QM.exists_equiv_torsion_and_forall_pushPt_eq_mulVec_of_forall_exists_eq_of_isMaximalOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/d29f990f-e937-5539-ba5f-2c122178f977
-- title:
--   N-torsion as a module over a maximal quaternion order
-- statement:
--   Fix natural numbers $r$ and $N$ with $r$ prime, $N \neq 0$ and $r \nmid N$, and an algebraically closed field $k_0$ in which $N$ is invertible ($(N : k_0) \neq 0$). Let $f : A \to \operatorname{Spec} k_0$ be a morphism of schemes equipped with a relative group law $L$, that is, a group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over each $t : T \to \operatorname{Spec} k_0$, natural in base change along $T' \to T$; assume $L$ is commutative, that $f$ satisfies the bundle of abelian-scheme properties (smooth, proper, connected fibres, and admitting a relative group law) and that $f$ is smooth of relative dimension $1$. Let $c, d \in \mathbb{Q}$ satisfy $c < 0$, $d < 0$ and the condition that for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},c,d] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra exactly when $r$ lies in $v$, and let $O \subseteq \mathbb{H}[\mathbb{Q},c,d]$ be a $\mathbb{Z}$-submodule which is an order (containing $1$, closed under multiplication, $\mathbb{Q}$-spanning, finitely generated) maximal among orders for inclusion. Let $\varepsilon$ assign to each $x \in O$ an endomorphism $\varepsilon x$ of $A$ over $\operatorname{Spec} k_0$ such that: each $\varepsilon x$ acts on $T$-points as a homomorphism for $L$; $\varepsilon$ sends $1$ to $\mathbb{1}_A$; $\varepsilon(xy)$ is $\varepsilon y$ followed by $\varepsilon x$; on points, pushforward by $\varepsilon(x+y)$ is the $L$-product of the pushforwards by $\varepsilon x$ and $\varepsilon y$; every endomorphism of $A$ over $\operatorname{Spec} k_0$ acting as an $L$-homomorphism on points equals some $\varepsilon x$; and $\varepsilon$ is injective. Then there exist a bijection $e_N$ from $\mathrm{Fin}\,2 \to \mathbb{Z}/N$ onto the set of points $Q$ over the geometric point $\operatorname{Spec}(\mathrm{id}_{k_0})$ whose $N$-fold $L$-sum is the identity point, and a map $\mu : O \to M_2(\mathbb{Z}/N)$, such that $e_N(v+w)$ is the $L$-product of $e_N(v)$ and $e_N(w)$, pushforward of $e_N(v)$ by $\varepsilon x$ equals $e_N(\mu(x)v)$, $\mu$ is surjective, and $\mu(x) = 0$ if and only if $x = N y$ in $\mathbb{H}[\mathbb{Q},c,d]$ for some $y \in O$.
--
--   This identifies the $N$-torsion of a one-dimensional abelian scheme over an algebraically closed field whose endomorphisms are exactly the maximal order $O$ in the definite quaternion algebra ramified only at $r$: the torsion is free of rank $2$ over $\mathbb{Z}/N$ and $O$ acts through a surjection $O \to M_2(\mathbb{Z}/N)$ with kernel $NO$, so that $O/NO \cong M_2(\mathbb{Z}/N)$ acts on it. It feeds the construction of fake elliptic curves with full level structure used in the Čerednik–Drinfel'd description of quaternionic moduli, being cited by [`CerednikDrinfeld.QM.exists_fakeEllipticCurve_isFormalModuleVia_hasHeight_four_endomorphismDictionary_endIsoFull_of_isUnit_two`](thm.html#CerednikDrinfeld.QM.exists_fakeEllipticCurve_isFormalModuleVia_hasHeight_four_endomorphismDictionary_endIsoFull_of_isUnit_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_equiv_torsion_and_forall_pushPt_eq_mulVec_of_forall_exists_eq_of_isMaximalOrder.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.exists_equiv_torsion_and_forall_pushPt_eq_mulVec_of_forall_exists_eq_of_isMaximalOrder
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (hN : (N : k₀) ≠ 0)
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k₀)) (L : RelativeGroupLaw k₀ f) (hLc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle k₀ f) (hA1 : SmoothOfRelativeDimension 1 f)
    {c d : ℚ} (hH' : IsDefiniteRamifiedExactlyAt c d r) (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsMaximalOrder O)
    (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f)
    (hε_hom : ∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t f),
      pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
    (hε_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, ε ⟨1, h⟩ = 𝟙 A)
    (hε_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
      ε ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t f),
      pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))

    (hEnd : ∀ (φ : A ⟶ A) (hφ : φ ≫ f = f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t f),
        mapPt φ hφ (L.mul t P Q) = L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) → ∃ x : ↥O, φ = ε x)
    (hε_inj : Function.Injective ε) :
    ∃ (eN : (Fin 2 → ZMod N) ≃
        {Q : SchemeHomOver (geomPoint k₀ (RingHom.id k₀)) f //
          nsmulPt L (geomPoint k₀ (RingHom.id k₀)) N Q = L.one (geomPoint k₀ (RingHom.id k₀))})
      (μ : ↥O → Matrix (Fin 2) (Fin 2) (ZMod N)),
      (∀ v w : Fin 2 → ZMod N,
        ((eN (v + w)) : SchemeHomOver (geomPoint k₀ (RingHom.id k₀)) f) =
          L.mul (geomPoint k₀ (RingHom.id k₀)) (eN v) (eN w)) ∧
      (∀ (x : ↥O) (v : Fin 2 → ZMod N),
        pushPt (ε x) (hε x) ((eN v) : SchemeHomOver (geomPoint k₀ (RingHom.id k₀)) f) = eN (Matrix.mulVec (μ x) v)) ∧
      Function.Surjective μ ∧
      (∀ x : ↥O, μ x = 0 ↔ ∃ y : ↥O, (x : ℍ[ℚ, c, d]) = (N : ℚ) • (y : ℍ[ℚ, c, d])) := by sorry
