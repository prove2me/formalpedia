-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_le_isOrder_forall_exists_pow_smul_mem_and_act_and_forall_exists_generalLinearGroup_and_exists_isMaximalOrder_inf_eq_of_isOrder_act_of_conj_of_injective
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_le_isOrder_forall_exists_pow_smul_mem_and_act_and_forall_exists_generalLinearGroup_and_exists_isMaximalOrder_inf_eq_of_isOrder_act_of_conj_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/818601fe-a630-56fd-a84a-e8c82986812c
-- title:
--   Endomorphism-ring export of the quaternionic formal-module dictionary
-- statement:
--   Fix a prime $r$ and a quaternion algebra $\mathbb H[\mathbb Q,a,b]$ together with a $\mathbb Z$-submodule $\Lambda$ of it which contains every rational integer (hypothesis `hΛℤ`), and a map $\mathrm{coord}:\Lambda\to W(\mathbb F_{r^2})\times W(\mathbb F_{r^2})$ satisfying `IsOrderCoord Λ r coord`: $\mathrm{coord}$ is additive, sends $1$ to $(1,0)$, is multiplicative for the twisted rule $(\alpha_1,\alpha_2)\cdot(\beta_1,\beta_2)=(\alpha_1\beta_1+r\,\alpha_2\varphi(\beta_2),\ \alpha_1\beta_2+\alpha_2\varphi(\beta_1))$ with $\varphi$ the Witt-vector Frobenius, is injective, has dense image modulo every power of $r$, and matches reduced traces: if $m+\bar m$ is the integer $n$ then $(\mathrm{coord}\,m)_1+\varphi((\mathrm{coord}\,m)_1)=n$.
--
--   The base is a commutative ring $B$ in which $r$ is nilpotent (`hq`). The geometric input is a fake elliptic curve $A_0$ of level $N$ over $B$ for $\Lambda$ — a scheme $A_0.A$ over $\operatorname{Spec} B$ which is smooth and proper with connected fibres of dimension $2$, equipped with a relative group law $A_0.L$ on its points over varying bases, a level map, and an action $m\mapsto A_0.\mathrm{act}\,m$ of $\Lambda$ by endomorphisms over the base which is additive, unital, anti-multiplicative and satisfies the trace condition on tangent spaces — together with a formal $\mathcal O_D$-module $X_0$ over $B$ (a commutative two-dimensional formal group law $X_0.F$ with an action of $W(\mathbb F_{r^2})$ and a uniformiser endomorphism $\varpi$ satisfying $\varpi\circ\varpi=[r]$ and $\varpi\circ\mathrm{act}(a)=\mathrm{act}(\varphi a)\circ\varpi$), a system $\theta_0$ of formal coordinates in two variables for $A_0.f$, and the hypothesis `hθ₀` that $\theta_0$ identifies the formal completion of $A_0.L$ with $X_0.F$ (functoriality in nilpotent $B$-algebras, bijectivity onto infinitesimal points, compatibility with the group laws) and transports the action of $m\in\Lambda$ to $\mathrm{act}((\mathrm{coord}\,m)_1)$ added, via $X_0.F$, to $\mathrm{act}((\mathrm{coord}\,m)_2)\circ\varpi$.
--
--   The second quaternion algebra is $H=\mathbb H[\mathbb Q,a_1,b_1]$ with $a_1\neq0$, $b_1\neq 0$. The acting order and its action: $R\subseteq H$ is an order (contains $1$, is closed under multiplication, spans $H$ over $\mathbb Q$, and is a finitely generated $\mathbb Z$-module), and $\varepsilon:R\to\operatorname{End}(A_0.A)$ satisfies the six clauses `hε`, `hε_hom`, `hε_lin`, `hε_one`, `hε_mul`, `hε_add`: each $\varepsilon(x)$ is an endomorphism over $\operatorname{Spec} B$, its push-forward on points over any base is a homomorphism for $A_0.L$, it commutes with every $A_0.\mathrm{act}\,m$, $\varepsilon(1)=\mathbf 1$, $\varepsilon(xy)=\varepsilon(y)$ followed by $\varepsilon(x)$ whenever $xy\in R$, and $\varepsilon(x+y)$ acts on points as the $A_0.L$-product of the actions of $\varepsilon(x)$ and $\varepsilon(y)$.
--
--   The group data: $\tilde\Gamma$ is a subgroup of $H^\times$, $u\in H^\times$, and $e:\tilde\Gamma\to\operatorname{End}(A_0.A)$ consists of endomorphisms over the base (`he`) such that for exponents $K(\gamma)\in\mathbb N$ and elements $x(\gamma)\in R$ one has $x(\gamma)=r^{K(\gamma)}\,u^{-1}\gamma u$ (`hx`) and $e(\gamma)=\varepsilon(x(\gamma))$ (`he_eq`).
--
--   The auxiliary lattices: $R_1$ is an order of $H$ and $R'$ a $\mathbb Z$-submodule, subject to two saturation hypotheses: for every $z\in R_1$ some $r^K u^{-1}zu$ lies in $R'$ (`hR₁R'`), and for every $y\in R'$ some $r^K y$ lies in $R$ with $\varepsilon(r^Ky)$ preserving the level structure, i.e. carrying points which factor through $A_0.\mathrm{lev}$ to points which factor through $A_0.\mathrm{lev}$ (`hR'R`).
--
--   The faithfulness and fullness hypotheses: $\varepsilon$ is injective (`hε_inj`); every endomorphism $\varphi$ of $A_0.A$ over the base whose push-forward on points is an $A_0.L$-homomorphism and which commutes with the $\Lambda$-action is of the form $\varepsilon(z)$, $z\in R$ (`hε_surj`); and for each prime $q\neq r$, every such $\varphi$ which annihilates all $q$-torsion points (those $P$ with $q\cdot P=A_0.L.\mathrm{one}$) factors as the action of $q$ followed by an endomorphism $\psi$ again homomorphic and $\Lambda$-linear (`hdivq`).
--
--   The twin-order hypotheses: $\Lambda_1$ and $\Lambda_1^{s}$ are $\mathbb Z$-submodules of $H$ with $\Lambda_1^{s}$ a maximal order (an order maximal among orders containing it), $R_1\le\Lambda_1^{s}$, and $\Lambda_1\cap\Lambda_1^{s}=R_1$ (`hΛ₁s`, `hR₁Λ₁s`, `htwin`); moreover for every $z\in\Lambda_1^{s}$ some $r^{K}u^{-1}zu$ lies in $R$ (`hΛ₁sR`), and for every $w\in R$ some $r^{K}uwu^{-1}$ lies in $\Lambda_1^{s}$ (`hRΛ₁s`). Finally $K_0$ is a field of characteristic zero and $\iota_0:H\to M_2(K_0)$ a $\mathbb Q$-algebra homomorphism.
--
--   The conclusion asserts the existence of a $\mathbb Z$-submodule $R_2\subseteq R_1$ which is an order, is $r$-saturated in $R_1$ (for every $z\in R_1$ there is $c$ with $r^cz\in R_2$), and of a map $\hat e:R_2\to\operatorname{End}(A_0.A)$ by endomorphisms over $\operatorname{Spec} B$, such that the following hold.
--
--   First, for each $z\in R_2$ the push-forward of $\hat e(z)$ on points is a homomorphism for $A_0.L$, it commutes with every $A_0.\mathrm{act}\,m$ for $m\in\Lambda$, and it preserves the level structure. Secondly, $\hat e(1)=\mathbf 1$ whenever $1\in R_2$. Thirdly, $\hat e(zy)=\hat e(y)$ followed by $\hat e(z)$ whenever $zy\in R_2$. Fourthly, for an integer $m$ lying in $R_2$ one has $\hat e(m)=A_0.\mathrm{act}\,m$. Fifthly, if $y,z\in R_2$ with $y=\bar z$ and $\mathrm{nrd}(z)=n_x\in\mathbb Z$, where $\mathrm{nrd}(x)=x_{\mathrm{re}}^2-a_1x_{I}^2-b_1x_{J}^2+a_1b_1x_{K}^2$, then $\hat e(y)$ followed by $\hat e(z)$ is $A_0.\mathrm{act}\,n_x$. Sixthly, $\hat e$ is compatible with $e$ up to powers of $r$: if $\gamma\in\tilde\Gamma$, $z\in R_2$ and $z=r^{k}\gamma$ for some $k$, then there are $i,j$ with $e(\gamma)$ followed by the action of $r^{i}$ equal to $\hat e(z)$ followed by the action of $r^{j}$.
--
--   Seventhly, a matrix description of both actions on the formal side: writing $\mathcal E$ for the centralizer, inside the endomorphism ring of $X_0.F$, of the set consisting of all $X_0.\mathrm{actEnd}$ together with $X_0.\varpi$, for every injective ring homomorphism $E_0:\mathcal E\to M_2(K_0)$ there is $g\in\mathrm{GL}_2(K_0)$ such that: for each $\gamma\in\tilde\Gamma$ there are $\varepsilon_X\in\mathcal E$ and $k_\gamma\in\mathbb Z$ with $\varepsilon_X$ inducing $e(\gamma)$ on the formal completion — for every $B$-algebra $B'$, ideal $J$ with $J^{m+1}=0$ and tuple $s$ of elements of $J$, $\theta_0$ evaluated at the truncated evaluation of the power series of $\varepsilon_X$ at $s$ equals the push-forward of $\theta_0(s)$ along $e(\gamma)$ — and with $E_0(\varepsilon_X)=r^{k_\gamma}\,g\,\iota_0(\gamma)\,g^{-1}$; and likewise for each $z\in R_2$ there are $\varepsilon_X\in\mathcal E$ and $k_x\in\mathbb Z$ with $\varepsilon_X$ inducing $\hat e(z)$ in the same sense and $E_0(\varepsilon_X)=r^{k_x}\,g\,\iota_0(z)\,g^{-1}$ (the same $g$ serving for all $\gamma$ and all $z$).
--
--   Eighthly, $R_2$ is stable under the quaternionic conjugation $z\mapsto\bar z$.
--
--   Ninthly, there exist a $\mathbb Z$-submodule again written $\Lambda_1^{s}$ (the binder shadows the hypothesis of the same name) which is a maximal order with $R_1\le\Lambda_1^{s}$ and $\Lambda_1\cap\Lambda_1^{s}=R_1$, an order $R_2'\le\Lambda_1^{s}$ which is $r$-saturated in $\Lambda_1^{s}$ (for every $z\in\Lambda_1^{s}$ some $r^cz\in R_2'$) and contains $R_2$, and a map $\hat e':R_2'\to\operatorname{End}(A_0.A)$ by endomorphisms over the base, such that: each $\hat e'(z)$ is homomorphic on points and commutes with the $\Lambda$-action (level preservation is not asserted here); $\hat e'(1)=\mathbf 1$ when $1\in R_2'$; $\hat e'(zy)=\hat e'(y)$ followed by $\hat e'(z)$ when $zy\in R_2'$; $\hat e'(m)=A_0.\mathrm{act}\,m$ for integers $m\in R_2'$; $\hat e'(\bar z)$ followed by $\hat e'(z)$ equals $A_0.\mathrm{act}\,n_z$ when $\mathrm{nrd}(z)=n_z\in\mathbb Z$; $\hat e'$ restricts to $\hat e$ on $R_2$; $R_2'$ is conjugation-stable; $\hat e'$ is injective; and, for each prime $q\neq r$ and each $z\in R_2'$ such that $\hat e'(z)$ annihilates all $q$-torsion points, there are $K\in\mathbb N$ and $y\in\Lambda_1^{s}$ with $r^{K}z=q\,y$.
--
--   This is the endomorphism-ring export of the Čerednik–Drinfeld dictionary between fake elliptic curves with formal $\mathcal O_D$-module structure over an $r$-nilpotent base and quaternionic lattice data: it replaces the given order $R$ and the maps $e$, $\varepsilon$ by an $r$-saturated suborder $R_2$ of $R_1$ acting by level-preserving, $\Lambda$-linear endomorphisms with the correct norm and conjugation relations, records the simultaneous conjugation of the actions of $\tilde\Gamma$ and $R_2$ into $\mathrm{GL}_2(K_0)$ by a single matrix $g$, and extends the action to an order $R_2'$ saturated in a maximal order $\Lambda_1^{s}$ twinned with $\Lambda_1$. It feeds the construction [`CerednikDrinfeld.QM.exists_fakeEllipticCurve_isFormalModuleVia_hasHeight_four_endomorphismDictionary_endIsoFull_of_isUnit_two`](thm.html#CerednikDrinfeld.QM.exists_fakeEllipticCurve_isFormalModuleVia_hasHeight_four_endomorphismDictionary_endIsoFull_of_isUnit_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_le_isOrder_forall_exists_pow_smul_mem_and_act_and_forall_exists_generalLinearGroup_and_exists_isMaximalOrder_inf_eq_of_isOrder_act_of_conj_of_injective.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld
  CerednikDrinfeld.SpecialFormal CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion MatrixGroups

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_le_isOrder_forall_exists_pow_smul_mem_and_act_and_forall_exists_generalLinearGroup_and_exists_isMaximalOrder_inf_eq_of_isOrder_act_of_conj_of_injective
    {r : ℕ} [Fact r.Prime]

    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord) {N : ℕ}

    {B : Type} [CommRing B] (hq : IsNilpotent (r : B))

    (A₀ : FakeEllipticCurve Λ N B) (X₀ : FormalODModule r B) (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (hθ₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    {a₁ b₁ : ℚ} (ha₁ : a₁ ≠ 0) (hb₁ : b₁ ≠ 0) (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR : IsOrder R)
    (ε : ↥R → (A₀.A ⟶ A₀.A)) (hε : ∀ x : ↥R, ε x ≫ A₀.f = A₀.f)
    (hε_hom : ∀ (x : ↥R) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
      pushPt (ε x) (hε x) (A₀.L.mul t P Q) = A₀.L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
    (hε_lin : ∀ (x : ↥R) (m : ↥Λ), A₀.act m ≫ ε x = ε x ≫ A₀.act m)
    (hε_one : ∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R, ε ⟨1, h⟩ = 𝟙 A₀.A)
    (hε_mul : ∀ (x y : ↥R) (h : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R),
      ε ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥R) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      pushPt (ε (x + y)) (hε (x + y)) P = A₀.L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))

    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (u : (ℍ[ℚ, a₁, b₁])ˣ)
    (e : ↥Γt → (A₀.A ⟶ A₀.A)) (he : ∀ γ, e γ ≫ A₀.f = A₀.f)
    (K : ↥Γt → ℕ) (x : ↥Γt → ↥R)
    (hx : ∀ γ : ↥Γt, (x γ : ℍ[ℚ, a₁, b₁]) =
      ((r ^ K γ : ℕ) : ℚ) • ((u⁻¹ * (γ : (ℍ[ℚ, a₁, b₁])ˣ) * u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]))
    (he_eq : ∀ γ : ↥Γt, e γ = ε (x γ))

    (R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₁ : IsOrder R₁) (R' : Submodule ℤ ℍ[ℚ, a₁, b₁])
    (hR₁R' : ∀ z : ↥R₁, ∃ K : ℕ,
      ((r ^ K : ℕ) : ℚ) • (((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * (z : ℍ[ℚ, a₁, b₁]) * ((u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) ∈ R')
    (hR'R : ∀ y : ↥R', ∃ (K : ℕ) (hK : ((r ^ K : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁]) ∈ R),
      FakeEllipticCurve.PreservesLevel A₀ A₀ (ε ⟨((r ^ K : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁]), hK⟩) (hε _))

    (hε_inj : ∀ z y : ↥R, ε z = ε y → z = y)
    (hε_surj : ∀ (φ : A₀.A ⟶ A₀.A) (hφ : φ ≫ A₀.f = A₀.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
        mapPt φ hφ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
      (∀ m : ↥Λ, A₀.act m ≫ φ = φ ≫ A₀.act m) → ∃ z : ↥R, φ = ε z)
    (hdivq : ∀ (q : ℕ), q.Prime → q ≠ r → ∀ (φ : A₀.A ⟶ A₀.A) (hφ : φ ≫ A₀.f = A₀.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
        mapPt φ hφ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
      (∀ m : ↥Λ, A₀.act m ≫ φ = φ ≫ A₀.act m) →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
        nsmulPt A₀.L t q P = A₀.L.one t → mapPt φ hφ P = A₀.L.one t) →
      ∃ (ψ : A₀.A ⟶ A₀.A) (hψ : ψ ≫ A₀.f = A₀.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
          mapPt ψ hψ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
        (∀ m : ↥Λ, A₀.act m ≫ ψ = ψ ≫ A₀.act m) ∧
        φ = A₀.act ⟨((q : ℤ) : ℚ), hΛℤ q⟩ ≫ ψ)
    (Λ₁ Λ₁s : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁s : IsMaximalOrder Λ₁s) (hR₁Λ₁s : R₁ ≤ Λ₁s) (htwin : Λ₁ ⊓ Λ₁s = R₁)
    (hΛ₁sR : ∀ z : ↥Λ₁s, ∃ K : ℕ,
      ((r ^ K : ℕ) : ℚ) • (((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * (z : ℍ[ℚ, a₁, b₁]) * ((u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) ∈ R)
    (hRΛ₁s : ∀ w : ↥R, ∃ K : ℕ,
      ((r ^ K : ℕ) : ℚ) • (((u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * (w : ℍ[ℚ, a₁, b₁]) * ((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) ∈ Λ₁s)

    (K₀ : Type) [Field K₀] [CharZero K₀] (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀) :
    ∃ (R₂ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₂ : R₂ ≤ R₁) (hR₂o : IsOrder R₂)
      (hR₂r : ∀ z : ↥R₁, ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • (z : ℍ[ℚ, a₁, b₁]) ∈ R₂)
      (ê : ↥R₂ → (A₀.A ⟶ A₀.A)) (hê : ∀ z, ê z ≫ A₀.f = A₀.f),

      (∀ z : ↥R₂,
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
            mapPt (ê z) (hê z) (A₀.L.mul t P Q) = A₀.L.mul t (mapPt (ê z) (hê z) P) (mapPt (ê z) (hê z) Q)) ∧
        (∀ m : ↥Λ, A₀.act m ≫ ê z = ê z ≫ A₀.act m) ∧
        FakeEllipticCurve.PreservesLevel A₀ A₀ (ê z) (hê z)) ∧

      (∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R₂, ê ⟨1, h⟩ = 𝟙 A₀.A) ∧
      (∀ (z y : ↥R₂) (h : (z : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R₂),
          ê ⟨(z : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ê y ≫ ê z) ∧
      (∀ (m : ℤ) (h : ((m : ℚ) : ℍ[ℚ, a₁, b₁]) ∈ R₂), ê ⟨((m : ℚ) : ℍ[ℚ, a₁, b₁]), h⟩ = A₀.act ⟨((m : ℤ) : ℚ), hΛℤ m⟩) ∧

      (∀ (z y : ↥R₂) (nx : ℤ), (y : ℍ[ℚ, a₁, b₁]) = star (z : ℍ[ℚ, a₁, b₁]) → nrd (z : ℍ[ℚ, a₁, b₁]) = (nx : ℚ) →
          ê y ≫ ê z = A₀.act ⟨((nx : ℤ) : ℚ), hΛℤ nx⟩) ∧

      (∀ (γ : ↥Γt) (z : ↥R₂) (k : ℕ),
          (z : ℍ[ℚ, a₁, b₁]) = ((r ^ k : ℕ) : ℚ) • ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) →
          ∃ i j : ℕ, e γ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ê z ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ∧

      (∀ E₀ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀, Function.Injective E₀ →
        ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀,
          (∀ γ : ↥Γt, ∃ (εX : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kγ : ℤ),
            (∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (m : ℕ),
                J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
                θ₀ B' (fun i => MvFormalGroup.nilEval m ((εX : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                  mapPt (e γ) (he γ) (θ₀ B' s)) ∧
            E₀ εX = ((r : K₀) ^ kγ) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
              ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))) ∧
          (∀ z : ↥R₂, ∃ (εX : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kx : ℤ),
            (∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (m : ℕ),
                J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
                θ₀ B' (fun i => MvFormalGroup.nilEval m ((εX : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                  mapPt (ê z) (hê z) (θ₀ B' s)) ∧
            E₀ εX = ((r : K₀) ^ kx) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ (z : ℍ[ℚ, a₁, b₁]) *
              ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)))) ∧

      (∀ z : ↥R₂, star (z : ℍ[ℚ, a₁, b₁]) ∈ R₂) ∧

      (∃ (Λ₁s : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁s : IsMaximalOrder Λ₁s) (hR₁Λ₁s : R₁ ≤ Λ₁s) (htwin : Λ₁ ⊓ Λ₁s = R₁)
          (R₂' : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₂' : R₂' ≤ Λ₁s) (hR₂'o : IsOrder R₂')
          (hR₂'r : ∀ z : ↥Λ₁s, ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • (z : ℍ[ℚ, a₁, b₁]) ∈ R₂') (hR₂R₂' : R₂ ≤ R₂')
          (ê' : ↥R₂' → (A₀.A ⟶ A₀.A)) (hê' : ∀ z, ê' z ≫ A₀.f = A₀.f),

        (∀ z : ↥R₂',
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
              mapPt (ê' z) (hê' z) (A₀.L.mul t P Q) = A₀.L.mul t (mapPt (ê' z) (hê' z) P) (mapPt (ê' z) (hê' z) Q)) ∧
          (∀ m : ↥Λ, A₀.act m ≫ ê' z = ê' z ≫ A₀.act m)) ∧

        (∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R₂', ê' ⟨1, h⟩ = 𝟙 A₀.A) ∧
        (∀ (z y : ↥R₂') (h : (z : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R₂'),
            ê' ⟨(z : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ê' y ≫ ê' z) ∧
        (∀ (m : ℤ) (h : ((m : ℚ) : ℍ[ℚ, a₁, b₁]) ∈ R₂'), ê' ⟨((m : ℚ) : ℍ[ℚ, a₁, b₁]), h⟩ = A₀.act ⟨((m : ℤ) : ℚ), hΛℤ m⟩) ∧

        (∀ (z y : ↥R₂') (nz : ℤ), (y : ℍ[ℚ, a₁, b₁]) = star (z : ℍ[ℚ, a₁, b₁]) → nrd (z : ℍ[ℚ, a₁, b₁]) = (nz : ℚ) →
            ê' y ≫ ê' z = A₀.act ⟨((nz : ℤ) : ℚ), hΛℤ nz⟩) ∧

        (∀ z : ↥R₂, ê' ⟨(z : ℍ[ℚ, a₁, b₁]), hR₂R₂' z.2⟩ = ê z) ∧

        (∀ z : ↥R₂', star (z : ℍ[ℚ, a₁, b₁]) ∈ R₂') ∧
        (∀ z y : ↥R₂', ê' z = ê' y → z = y) ∧

        (∀ (q : ℕ), q.Prime → q ≠ r → ∀ z : ↥R₂',
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
              nsmulPt A₀.L t q P = A₀.L.one t → mapPt (ê' z) (hê' z) P = A₀.L.one t) →
          ∃ (K : ℕ) (y : ↥Λ₁s), ((r ^ K : ℕ) : ℚ) • (z : ℍ[ℚ, a₁, b₁]) = (q : ℚ) • (y : ℍ[ℚ, a₁, b₁]))) := by sorry
