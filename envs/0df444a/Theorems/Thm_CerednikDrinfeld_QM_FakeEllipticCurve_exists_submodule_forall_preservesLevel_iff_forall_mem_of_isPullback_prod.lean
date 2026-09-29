-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_submodule_forall_preservesLevel_iff_forall_mem_of_isPullback_prod
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_submodule_forall_preservesLevel_iff_forall_mem_of_isPullback_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/a1bca166-4538-5dab-a1df-154de0a3bd7f
-- title:
--   Level preservation detected on a coordinate submodule W
-- statement:
--   Fix primes $r \ne \bar r$ and $N \ne 0$ with $N$ squarefree and divisible by neither $r$ nor $\bar r$, and an algebraically closed field $k_0$ with $N \ne 0$ in $k_0$. Let $\mathbb{H}[\mathbb{Q},a,b]$ satisfy `IsIndefiniteRamifiedExactlyAt a b r rbar` ($0<a$ or $0<b$, and the finite places at which the algebra stays a division algebra after completion are exactly those containing $r$ or $\bar r$), let $\Lambda$ be a maximal order in it, and let $A_0$ be a `FakeEllipticCurve Λ N k₀`. Further data: a scheme $A$ with structure morphism $f$ to $\operatorname{Spec} k_0$ and a relative group law $L$; a maximal order $O$ in a definite $\mathbb{H}[\mathbb{Q},c,d]$ ramified exactly at $r$, acting on $A$ over $f$ by endomorphisms $\varepsilon$ that are additive for $L$, send $1$ to the identity, satisfy $\varepsilon(xy)=\varepsilon(y)$ followed by $\varepsilon(x)$, and are additive in the argument; a bijection $e_N$ from $(\mathbb{Z}/N)^2$ onto the $N$-torsion of $L$ at the geometric point $\operatorname{Spec} k_0 \to \operatorname{Spec} k_0$ (identity), additive, and equivariant for a surjective map $\mu : O \to M_2(\mathbb{Z}/N)$ whose kernel is $N\cdot O$; a $\mathbb{Q}$-algebra map $j : \mathbb{H}[\mathbb{Q},a,b] \to M_2(\mathbb{H}[\mathbb{Q},c,d])$ carrying $\Lambda$ into $M_2(O)$; morphisms $p_1,p_2 : A_0.A \to A$ over $k_0$ exhibiting $A_0.A$ as the pullback of $f$ along $f$ and compatible with the group laws; an action $E$ of matrices with entries in $O$ on $A_0.A$ over its structure morphism, satisfying the block formula expressing $p_i \circ E(y)$ through $\varepsilon$ of the entries $y_{i0}, y_{i1}$ and $p_1, p_2$, with $A_0.\mathrm{act}(m) = E(j(m))$, and additive, unital and anti-multiplicative as above; and finally a definite $\mathbb{H}[\mathbb{Q},a_1,b_1]$ ramified exactly at $\bar r$ with an injective $\mathbb{Q}$-algebra map $\tau$ into $M_2(\mathbb{H}[\mathbb{Q},c,d])$ whose image is exactly the centraliser of $j(\mathbb{H}[\mathbb{Q},a,b])$, together with $R = \{x : \text{all entries of } \tau x \text{ lie in } O\}$. The conclusion asserts the existence of a $\mathbb{Z}/N$-submodule $W$ of $2 \times 2$ matrices over $\mathbb{Z}/N$ such that: for every point $Q$ of $A_0$ over the geometric point and every $w$ with $p_1 \circ Q = e_N(w_0)$ and $p_2 \circ Q = e_N(w_1)$, one has $w \in W$ if and only if $Q$ factors through $A_0.\mathrm{lev}$; $W$ is stable under the block operator $w \mapsto (i \mapsto \sum_l \mu(j(m)_{il})w_l)$ for all $m \in \Lambda$; $W$ has exactly $N^2$ elements; and for every $x \in R$ the endomorphism $E(\tau x)$ of $A_0$ preserves the level (every point factoring through $A_0.\mathrm{lev}$ has image again factoring through it) if and only if the block operator attached to $\tau x$ maps $W$ into $W$.
--
--   This is the step that converts the scheme-theoretic condition of preserving the level structure on a fake elliptic curve, which quantifies over all $T$-points, into a purely linear-algebraic condition on a distinguished submodule $W$ of $M_2(\mathbb{Z}/N)$ recording the $N$-torsion coordinates of the level subscheme; the passage to $k_0$-points uses the criterion `preservesLevel_iff_forall_factorsThrough_geomPoint_of_isAlgClosed`. It is used in the Čerednik–Drinfel'd comparison to identify the ring of level-preserving endomorphisms coming from the centralising definite algebra as an Eichler order.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_submodule_forall_preservesLevel_iff_forall_mem_of_isPullback_prod.lean

import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_submodule_forall_preservesLevel_iff_forall_mem_of_isPullback_prod
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N)
    (hN : Squarefree N)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (hNk : (N : k₀) ≠ 0)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (A₀ : FakeEllipticCurve Λ N k₀)

    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k₀)) (L : RelativeGroupLaw k₀ f)
    {c d : ℚ} (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsOrder O)
    (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f)
    (hε_hom : ∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t f),
      pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
    (hε_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, ε ⟨1, h⟩ = 𝟙 A)
    (hε_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
      ε ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t f),
      pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    (hH' : IsDefiniteRamifiedExactlyAt c d r) (hOmax : IsMaximalOrder O)

    (eN : (Fin 2 → ZMod N) ≃
        {Q : SchemeHomOver (geomPoint k₀ (RingHom.id k₀)) f //
          nsmulPt L (geomPoint k₀ (RingHom.id k₀)) N Q = L.one (geomPoint k₀ (RingHom.id k₀))})
    (μ : ↥O → Matrix (Fin 2) (Fin 2) (ZMod N))
    (heN_add : ∀ v w : Fin 2 → ZMod N,
      ((eN (v + w)) : SchemeHomOver (geomPoint k₀ (RingHom.id k₀)) f) = L.mul (geomPoint k₀ (RingHom.id k₀)) (eN v) (eN w))
    (heN_act : ∀ (x : ↥O) (v : Fin 2 → ZMod N),
      pushPt (ε x) (hε x) ((eN v) : SchemeHomOver (geomPoint k₀ (RingHom.id k₀)) f) = eN (Matrix.mulVec (μ x) v))
    (hμ_surj : Function.Surjective μ)
    (hμ_ker : ∀ x : ↥O, μ x = 0 ↔ ∃ y : ↥O, (x : ℍ[ℚ, c, d]) = (N : ℚ) • (y : ℍ[ℚ, c, d]))

    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O)
    (p₁ p₂ : A₀.A ⟶ A) (hp₁ : p₁ ≫ f = A₀.f) (hp₂ : p₂ ≫ f = A₀.f) (hpb : CategoryTheory.IsPullback p₁ p₂ f f)
    (hp_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      mapPt p₁ hp₁ (A₀.L.mul t P Q) = L.mul t (mapPt p₁ hp₁ P) (mapPt p₁ hp₁ Q) ∧
      mapPt p₂ hp₂ (A₀.L.mul t P Q) = L.mul t (mapPt p₂ hp₂ P) (mapPt p₂ hp₂ Q))
    (E : ∀ y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], (∀ i l, y i l ∈ O) → (A₀.A ⟶ A₀.A))
    (hE : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O), E y hy ≫ A₀.f = A₀.f)
    (hE_mat : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O)
        {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t A₀.f),
      mapPt p₁ hp₁ (pushPt (E y hy) (hE y hy) P) =
        L.mul t (pushPt (ε ⟨y 0 0, hy 0 0⟩) (hε _) (mapPt p₁ hp₁ P)) (pushPt (ε ⟨y 0 1, hy 0 1⟩) (hε _) (mapPt p₂ hp₂ P)) ∧
      mapPt p₂ hp₂ (pushPt (E y hy) (hE y hy) P) =
        L.mul t (pushPt (ε ⟨y 1 0, hy 1 0⟩) (hε _) (mapPt p₁ hp₁ P)) (pushPt (ε ⟨y 1 1, hy 1 1⟩) (hε _) (mapPt p₂ hp₂ P)))
    (hact : ∀ m : ↥Λ, A₀.act m = E (j (m : ℍ[ℚ, a, b])) (hj m))
    (hE_hom : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O)
        {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      pushPt (E y hy) (hE y hy) (A₀.L.mul t P Q) = A₀.L.mul t (pushPt (E y hy) (hE y hy) P) (pushPt (E y hy) (hE y hy) Q))
    (hE_one : ∀ h1 : ∀ i l, (1 : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) i l ∈ O, E 1 h1 = 𝟙 A₀.A)
    (hE_mul : ∀ (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
        (hyy' : ∀ i l, (y * y') i l ∈ O), E (y * y') hyy' = E y' hy' ≫ E y hy)
    (hE_add : ∀ (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
        (hyy' : ∀ i l, (y + y') i l ∈ O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t A₀.f),
      pushPt (E (y + y') hyy') (hE _ hyy') P = A₀.L.mul t (pushPt (E y hy) (hE y hy) P) (pushPt (E y' hy') (hE y' hy') P))

    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a₁ b₁ rbar)
    (τ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hτ : Function.Injective τ)
    (hτc : ∀ y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], (∀ m : ℍ[ℚ, a, b], y * j m = j m * y) ↔ y ∈ Set.range τ)
    (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hRiff : ∀ x : ℍ[ℚ, a₁, b₁], x ∈ R ↔ ∀ i l : Fin 2, τ x i l ∈ O) :
    ∃ W : Submodule (ZMod N) (Fin 2 → Fin 2 → ZMod N),

      (∀ (Q : SchemeHomOver (geomPoint k₀ (RingHom.id k₀)) A₀.f) (w : Fin 2 → Fin 2 → ZMod N),
          mapPt p₁ hp₁ Q = ((eN (w 0)) : SchemeHomOver (geomPoint k₀ (RingHom.id k₀)) f) →
          mapPt p₂ hp₂ Q = ((eN (w 1)) : SchemeHomOver (geomPoint k₀ (RingHom.id k₀)) f) →
          (w ∈ W ↔ FactorsThrough A₀.lev Q)) ∧

      (∀ (m : ↥Λ) (w : Fin 2 → Fin 2 → ZMod N), w ∈ W →
          (fun i => ∑ l, Matrix.mulVec (μ ⟨j (m : ℍ[ℚ, a, b]) i l, hj m i l⟩) (w l)) ∈ W) ∧
      Nat.card ↥W = N ^ 2 ∧

      (∀ (x : ℍ[ℚ, a₁, b₁]) (hx : x ∈ R),
          FakeEllipticCurve.PreservesLevel A₀ A₀ (E (τ x) ((hRiff x).1 hx)) (hE _ ((hRiff x).1 hx)) ↔
            ∀ w : Fin 2 → Fin 2 → ZMod N, w ∈ W → (fun i => ∑ l, Matrix.mulVec (μ ⟨τ x i l, (hRiff x).1 hx i l⟩) (w l)) ∈ W) := by sorry
