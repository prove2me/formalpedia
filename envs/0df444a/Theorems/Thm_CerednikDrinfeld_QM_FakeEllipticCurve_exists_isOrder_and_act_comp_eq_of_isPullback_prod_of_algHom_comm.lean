-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isOrder_and_act_comp_eq_of_isPullback_prod_of_algHom_comm
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isOrder_and_act_comp_eq_of_isPullback_prod_of_algHom_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/badd3635-ef10-5d8d-8e28-41c85ae1633b
-- title:
--   Centraliser order acting on a fake elliptic curve
-- statement:
--   Fix $N\in\mathbb N$, a commutative ring $S$, rationals $a,b$, a $\mathbb Z$-submodule $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ and a fake elliptic curve $A_0$ of level $N$ over $S$ for $\Lambda$. Let $f\colon A\to\operatorname{Spec}S$ be a scheme over $S$ carrying a relative group law $L$ (a functorial group structure on the sets of $T$-points over $S$), let $O\subseteq\mathbb H[\mathbb Q,c,d]$ be a $\mathbb Z$-submodule that is an order (contains $1$, is closed under multiplication, spans the algebra over $\mathbb Q$ and is finitely generated), and let $\varepsilon$ assign to each $x\in O$ an endomorphism $\varepsilon x$ of $A$ over $S$ which is additive on points for $L$, with $\varepsilon 1=\mathrm{id}$, $\varepsilon(xy)=\varepsilon y$ followed by $\varepsilon x$, and $\varepsilon(x+y)$ equal to the $L$-product of $\varepsilon x$ and $\varepsilon y$ on points. Let $j\colon\mathbb H[\mathbb Q,a,b]\to M_2(\mathbb H[\mathbb Q,c,d])$ be a $\mathbb Q$-algebra map whose values on $\Lambda$ have all entries in $O$, let $p_1,p_2\colon A_0.A\to A$ be maps over $S$ exhibiting $A_0.A$ as the pullback of $f$ along $f$ and additive on points, and let $E$ assign to each matrix $y\in M_2(\mathbb H[\mathbb Q,c,d])$ with entries in $O$ an endomorphism $E\,y$ of $A_0.A$ over $S$ such that $p_1,p_2$ transport $E\,y$ into the two rows $(\varepsilon y_{00},\varepsilon y_{01})$, $(\varepsilon y_{10},\varepsilon y_{11})$ of $\varepsilon$-combinations, such that $A_0.\mathrm{act}(m)=E(j m)$ for $m\in\Lambda$, and such that $E$ is additive on points, sends $1$ to the identity, and satisfies $E(yy')=E\,y'$ followed by $E\,y$ and additivity in $y$. Finally let $\tau\colon\mathbb H[\mathbb Q,a_1,b_1]\to M_2(\mathbb H[\mathbb Q,c,d])$ be an injective $\mathbb Q$-algebra map with $\tau(x)j(m)=j(m)\tau(x)$ for all $x$ and $m$. Then there is a $\mathbb Z$-submodule $R\subseteq\mathbb H[\mathbb Q,a_1,b_1]$ consisting exactly of those $x$ with all entries of $\tau x$ in $O$, which is an order, and the assignment $x\mapsto E(\tau x)$ for $x\in R$ consists of endomorphisms of $A_0.A$ over $A_0.f$ that are additive on points, commute with $A_0.\mathrm{act}(m)$ for every $m\in\Lambda$, send $1$ to the identity of $A_0.A$, satisfy $E(\tau(xy))=E(\tau y)$ followed by $E(\tau x)$, and satisfy $E(\tau(x+y))$ equal to the $L$-product of $E(\tau x)$ and $E(\tau y)$ on points.
--
--   This produces the order $R=\tau^{-1}(M_2(O))$ in a second quaternion algebra, the centraliser of the given $\Lambda$-action on a product $A\times_S A$, together with its action on the fake elliptic curve $A_0$ by endomorphisms commuting with that of $\Lambda$. It is used in the construction of fake elliptic curves whose endomorphism algebra realises the prescribed dictionary of quaternionic endomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isOrder_and_act_comp_eq_of_isPullback_prod_of_algHom_comm.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isOrder_and_act_comp_eq_of_isPullback_prod_of_algHom_comm
    {N : ℕ} (S : Type) [CommRing S]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (A₀ : FakeEllipticCurve Λ N S)

    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {c d : ℚ} (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsOrder O)
    (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f)
    (hε_hom : ∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
    (hε_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, ε ⟨1, h⟩ = 𝟙 A)
    (hε_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
      ε ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))

    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O)
    (p₁ p₂ : A₀.A ⟶ A) (hp₁ : p₁ ≫ f = A₀.f) (hp₂ : p₂ ≫ f = A₀.f) (hpb : CategoryTheory.IsPullback p₁ p₂ f f)
    (hp_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A₀.f),
      mapPt p₁ hp₁ (A₀.L.mul t P Q) = L.mul t (mapPt p₁ hp₁ P) (mapPt p₁ hp₁ Q) ∧
      mapPt p₂ hp₂ (A₀.L.mul t P Q) = L.mul t (mapPt p₂ hp₂ P) (mapPt p₂ hp₂ Q))
    (E : ∀ y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], (∀ i l, y i l ∈ O) → (A₀.A ⟶ A₀.A))
    (hE : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O), E y hy ≫ A₀.f = A₀.f)
    (hE_mat : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O)
        {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t A₀.f),
      mapPt p₁ hp₁ (pushPt (E y hy) (hE y hy) P) =
        L.mul t (pushPt (ε ⟨y 0 0, hy 0 0⟩) (hε _) (mapPt p₁ hp₁ P)) (pushPt (ε ⟨y 0 1, hy 0 1⟩) (hε _) (mapPt p₂ hp₂ P)) ∧
      mapPt p₂ hp₂ (pushPt (E y hy) (hE y hy) P) =
        L.mul t (pushPt (ε ⟨y 1 0, hy 1 0⟩) (hε _) (mapPt p₁ hp₁ P)) (pushPt (ε ⟨y 1 1, hy 1 1⟩) (hε _) (mapPt p₂ hp₂ P)))
    (hact : ∀ m : ↥Λ, A₀.act m = E (j (m : ℍ[ℚ, a, b])) (hj m))
    (hE_hom : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O)
        {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A₀.f),
      pushPt (E y hy) (hE y hy) (A₀.L.mul t P Q) = A₀.L.mul t (pushPt (E y hy) (hE y hy) P) (pushPt (E y hy) (hE y hy) Q))
    (hE_one : ∀ h1 : ∀ i l, (1 : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) i l ∈ O, E 1 h1 = 𝟙 A₀.A)
    (hE_mul : ∀ (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
        (hyy' : ∀ i l, (y * y') i l ∈ O), E (y * y') hyy' = E y' hy' ≫ E y hy)
    (hE_add : ∀ (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
        (hyy' : ∀ i l, (y + y') i l ∈ O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t A₀.f),
      pushPt (E (y + y') hyy') (hE _ hyy') P = A₀.L.mul t (pushPt (E y hy) (hE y hy) P) (pushPt (E y' hy') (hE y' hy') P))

    {a₁ b₁ : ℚ} (τ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hτ : Function.Injective τ)
    (hτj : ∀ (x : ℍ[ℚ, a₁, b₁]) (m : ℍ[ℚ, a, b]), τ x * j m = j m * τ x) :
    ∃ R : Submodule ℤ ℍ[ℚ, a₁, b₁],
      (∀ x : ℍ[ℚ, a₁, b₁], x ∈ R ↔ ∀ i l : Fin 2, τ x i l ∈ O) ∧
      ∃ (hR : IsOrder R) (hRO : ∀ (x : ↥R) (i l : Fin 2), τ (x : ℍ[ℚ, a₁, b₁]) i l ∈ O),
        (∀ x : ↥R, E (τ (x : ℍ[ℚ, a₁, b₁])) (hRO x) ≫ A₀.f = A₀.f) ∧
        (∀ (x : ↥R) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A₀.f),
          pushPt (E (τ (x : ℍ[ℚ, a₁, b₁])) (hRO x)) (hE _ (hRO x)) (A₀.L.mul t P Q) =
            A₀.L.mul t (pushPt (E (τ (x : ℍ[ℚ, a₁, b₁])) (hRO x)) (hE _ (hRO x)) P)
              (pushPt (E (τ (x : ℍ[ℚ, a₁, b₁])) (hRO x)) (hE _ (hRO x)) Q)) ∧
        (∀ (x : ↥R) (m : ↥Λ), A₀.act m ≫ E (τ (x : ℍ[ℚ, a₁, b₁])) (hRO x) = E (τ (x : ℍ[ℚ, a₁, b₁])) (hRO x) ≫ A₀.act m) ∧
        (∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R, E (τ ((⟨1, h⟩ : ↥R) : ℍ[ℚ, a₁, b₁])) (hRO ⟨1, h⟩) = 𝟙 A₀.A) ∧
        (∀ (x y : ↥R) (h : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R),
          E (τ ((⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ : ↥R) : ℍ[ℚ, a₁, b₁])) (hRO ⟨_, h⟩) =
            E (τ (y : ℍ[ℚ, a₁, b₁])) (hRO y) ≫ E (τ (x : ℍ[ℚ, a₁, b₁])) (hRO x)) ∧
        (∀ (x y : ↥R) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t A₀.f),
          pushPt (E (τ ((x + y : ↥R) : ℍ[ℚ, a₁, b₁])) (hRO (x + y))) (hE _ (hRO (x + y))) P =
            A₀.L.mul t (pushPt (E (τ (x : ℍ[ℚ, a₁, b₁])) (hRO x)) (hE _ (hRO x)) P)
              (pushPt (E (τ (y : ℍ[ℚ, a₁, b₁])) (hRO y)) (hE _ (hRO y)) P)) := by sorry
