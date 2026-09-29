-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_fakeEllipticCurve_one_isPullback_and_act_eq_of_act_of_algHom_matrix_of_trace
-- name    : CerednikDrinfeld.QM.exists_fakeEllipticCurve_one_isPullback_and_act_eq_of_act_of_algHom_matrix_of_trace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/7a7af042-69f7-50c8-ab99-4deeacba90e9
-- title:
--   The square A×_k A as a fake elliptic curve
-- statement:
--   Let $q$ be a prime and $k$ a field of characteristic $q$. Let $f : A \to \operatorname{Spec} k$ be a morphism of schemes carrying a relative group law $L$ (functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $k$, compatible with base change) which is commutative, and assume $f$ satisfies the abelian-scheme property bundle (smooth, proper, connected fibres, a relative group law exists) and is smooth of relative dimension $1$. Let $c,d \in \mathbb{Q}$ and let $O \subseteq \mathbb{H}[\mathbb{Q},c,d]$ be an order (a finitely generated $\mathbb{Z}$-submodule containing $1$, closed under multiplication, spanning the algebra over $\mathbb{Q}$). Let $\varepsilon$ assign to each $x \in O$ an endomorphism $\varepsilon x$ of $A$ over $f$, such that each $\varepsilon x$ is a homomorphism for $L$ on $T$-points, $\varepsilon 1 = \mathrm{id}_A$, $\varepsilon(xy) = \varepsilon y$ followed by $\varepsilon x$, and $\varepsilon(x+y)$ acts on points as the $L$-product of $\varepsilon x$ and $\varepsilon y$. Let $a,b \in \mathbb{Q}$, let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be an order, and let $j : \mathbb{H}[\mathbb{Q},a,b] \to M_2(\mathbb{H}[\mathbb{Q},c,d])$ be a $\mathbb{Q}$-algebra map with all entries of $j(m)$ in $O$ for $m \in \Lambda$. Assume the trace condition: for every field $F$ of characteristic $q$ and every $\chi : O \to F$ with $\chi(1) = 1$, additive and multiplicative, and every $m \in \Lambda$ and $n \in \mathbb{Z}$ with $m + \bar m = n$, one has $\chi(j(m)_{00}) + \chi(j(m)_{11}) = n$ in $F$. Then there exist a fake elliptic curve $A_0$ of type $(\Lambda, 1)$ over $k$ (a scheme with structure morphism to $\operatorname{Spec} k$, a commutative relative group law, the abelian-scheme property bundle, fibres of topological Krull dimension $2$, a $\Lambda$-action by endomorphisms satisfying the analogous unit, anti-multiplicativity, additivity and trace conditions, together with its level data), morphisms $p_1, p_2 : A_0.A \to A$ over $k$, and for each matrix $y \in M_2(\mathbb{H}[\mathbb{Q},c,d])$ with all entries in $O$ an endomorphism $E(y)$ of $A_0.A$ over $A_0.f$, such that: the square formed by $p_1, p_2, f, f$ is cartesian, so $A_0.A \cong A \times_k A$; both $p_1$ and $p_2$ are homomorphisms from the group law of $A_0$ to $L$ on $T$-points; for every admissible $y$ and every point $P$, $p_i \circ E(y)(P)$ is the $L$-product of $\varepsilon(y_{i0})$ applied to $p_1 \circ P$ and $\varepsilon(y_{i1})$ applied to $p_2 \circ P$, for $i = 1,2$; $A_0.\mathrm{act}(m) = E(j(m))$ for all $m \in \Lambda$; and $E$ itself is a homomorphism on points, with $E(1) = \mathrm{id}$, $E(yy') = E(y')$ followed by $E(y)$, and $E(y+y')$ acting on points as the $L$-product of $E(y)$ and $E(y')$.
--
--   This is Shimura's construction of a quaternionic abelian surface as the square $A \times_k A$ of an elliptic curve, in the form needed when the matrix algebra $M_2(\mathbb{H}[\mathbb{Q},c,d])$ receives the quaternion order $\Lambda$ through $j$: it produces the fake elliptic curve together with the product decomposition and the whole $M_2(O)$-action, not merely the existence of a fake elliptic curve. The extra data are what the supersingular endomorphism dictionary uses, since endomorphisms $E(y)$ for $y$ centralising $j(\Lambda)$ then commute with the $\Lambda$-action; the result is cited by the theorem producing a fake elliptic curve with a formal module of height four and a full endomorphism dictionary.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_fakeEllipticCurve_one_isPullback_and_act_eq_of_act_of_algHom_matrix_of_trace.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open GoodReductionJacobian
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.exists_fakeEllipticCurve_one_isPullback_and_act_eq_of_act_of_algHom_matrix_of_trace
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (hLc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle k f) (hA1 : SmoothOfRelativeDimension 1 f)
    {c d : ℚ} (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsOrder O)
    (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f)
    (hε_hom : ∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
    (hε_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, ε ⟨1, h⟩ = 𝟙 A)
    (hε_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
      ε ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
      pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d])
    (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O)
    (hj_trace : ∀ (F : Type) [Field F] [CharP F q] (χ : ↥O → F),
      (∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, χ ⟨1, h⟩ = 1) →
      (∀ x y : ↥O, χ (x + y) = χ x + χ y) →
      (∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
        χ ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = χ x * χ y) →
      ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
        χ ⟨j (m : ℍ[ℚ, a, b]) 0 0, hj m 0 0⟩ + χ ⟨j (m : ℍ[ℚ, a, b]) 1 1, hj m 1 1⟩ = (n : F)) :
    ∃ (A₀ : FakeEllipticCurve Λ 1 k) (p₁ p₂ : A₀.A ⟶ A) (hp₁ : p₁ ≫ f = A₀.f) (hp₂ : p₂ ≫ f = A₀.f)
      (E : ∀ y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], (∀ i l, y i l ∈ O) → (A₀.A ⟶ A₀.A))
      (hE : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O), E y hy ≫ A₀.f = A₀.f),

      CategoryTheory.IsPullback p₁ p₂ f f ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t A₀.f),
        mapPt p₁ hp₁ (A₀.L.mul t P Q) = L.mul t (mapPt p₁ hp₁ P) (mapPt p₁ hp₁ Q) ∧
        mapPt p₂ hp₂ (A₀.L.mul t P Q) = L.mul t (mapPt p₂ hp₂ P) (mapPt p₂ hp₂ Q)) ∧

      (∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O)
          {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A₀.f),
        mapPt p₁ hp₁ (pushPt (E y hy) (hE y hy) P) =
          L.mul t (pushPt (ε ⟨y 0 0, hy 0 0⟩) (hε _) (mapPt p₁ hp₁ P)) (pushPt (ε ⟨y 0 1, hy 0 1⟩) (hε _) (mapPt p₂ hp₂ P)) ∧
        mapPt p₂ hp₂ (pushPt (E y hy) (hE y hy) P) =
          L.mul t (pushPt (ε ⟨y 1 0, hy 1 0⟩) (hε _) (mapPt p₁ hp₁ P)) (pushPt (ε ⟨y 1 1, hy 1 1⟩) (hε _) (mapPt p₂ hp₂ P))) ∧

      (∀ m : ↥Λ, A₀.act m = E (j (m : ℍ[ℚ, a, b])) (hj m)) ∧

      (∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O)
          {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t A₀.f),
        pushPt (E y hy) (hE y hy) (A₀.L.mul t P Q) = A₀.L.mul t (pushPt (E y hy) (hE y hy) P) (pushPt (E y hy) (hE y hy) Q)) ∧
      (∀ h1 : ∀ i l, (1 : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) i l ∈ O, E 1 h1 = 𝟙 A₀.A) ∧
      (∀ (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
          (hyy' : ∀ i l, (y * y') i l ∈ O), E (y * y') hyy' = E y' hy' ≫ E y hy) ∧
      (∀ (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
          (hyy' : ∀ i l, (y + y') i l ∈ O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A₀.f),
        pushPt (E (y + y') hyy') (hE _ hyy') P = A₀.L.mul t (pushPt (E y hy) (hE y hy) P) (pushPt (E y' hy') (hE y' hy') P)) := by sorry
