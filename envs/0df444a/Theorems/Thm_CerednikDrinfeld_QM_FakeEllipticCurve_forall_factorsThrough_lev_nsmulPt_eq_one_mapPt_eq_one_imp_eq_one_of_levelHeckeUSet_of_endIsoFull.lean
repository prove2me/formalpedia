-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_forall_factorsThrough_lev_nsmulPt_eq_one_mapPt_eq_one_imp_eq_one_of_levelHeckeUSet_of_endIsoFull
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.forall_factorsThrough_lev_nsmulPt_eq_one_mapPt_eq_one_imp_eq_one_of_levelHeckeUSet_of_endIsoFull
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/eb4e548b-3cf4-5e93-9fe1-c9127c234b0e
-- title:
--   Level sections killed by ℓ and by ̂ e(r^m̄ s) vanish
-- statement:
--   Fix primes $r,\bar r$ with $\bar r\neq r$ and a nonzero squarefree $N$ divisible by neither, rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies $0<a$ or $0<b$ and is a division algebra over $\mathbb{Q}_v$ exactly at the height-one primes $v$ of $\mathcal{O}_{\mathbb{Q}}$ containing $r$ or $\bar r$, a maximal order $\Lambda$ (an order maximal among orders containing it) with $\mathbb{Z}\subseteq\Lambda$, an algebraically closed field $k_0$ of characteristic $r$, and $A_0$ a `FakeEllipticCurve` for $(\Lambda,N)$ over $k_0$, with structure morphism $A_0.f$, relative group law $A_0.L$ and level morphism $A_0.\mathrm{lev}$. On the definite side fix $a_1,b_1<0$ with $\mathbb{H}[\mathbb{Q},a_1,b_1]$ ramified exactly at $\bar r$, a maximal order $\Lambda_1$, an Eichler order $R_1$ of level $N$ (an intersection of two maximal orders of relative index $N$ in the first) with $R_1\le\Lambda_1$, a prime $v$ containing $r$, a maximal order $\Lambda_1^{s}$ with $R_1\le\Lambda_1^{s}$ and $\Lambda_1\cap\Lambda_1^{s}=R_1$, and orders $R_2\le R_1$, $R_2'\le\Lambda_1^{s}$ with $R_2\le R_2'$ such that every element of $R_1$ (respectively $\Lambda_1^{s}$) becomes an element of $R_2$ (respectively $R_2'$) after scaling by a power of $r$. The endomorphism data are maps $\hat e:R_2\to\operatorname{End}(A_0.A)$ and $\hat e':R_2'\to\operatorname{End}(A_0.A)$ over $\operatorname{Spec}k_0$, subject to: additivity for the group law on sections, commutation with the $\Lambda$-action, $\hat e(1)=\mathrm{id}$, $\hat e(xy)=\hat e(y)$ followed by $\hat e(x)$, agreement with $A_0.\mathrm{act}$ on rational integers, stability of $R_2$ and $R_2'$ under `star`, preservation of factorisation through $A_0.\mathrm{lev}$ by each $\hat e(x)$, the norm relation $\hat e'(\bar z)$ followed by $\hat e'(z)$ equals the action of $\mathrm{nrd}(z)\in\mathbb{Z}$, the compatibility $\hat e'|_{R_2}=\hat e$, injectivity of $\hat e'$, and the faithfulness clause that for a prime $q\neq r$, if $\hat e'(z)$ annihilates all $q$-torsion sections then $r^{K}z\in q\Lambda_1^{s}$ for some $K$. The Hecke datum consists of $n_1\in\operatorname{primeHeckeSet}R_1\,r$ with $\operatorname{meetOrder}R_1\,n_1=R_1\cap n_1R_1n_1^{-1}$ an Eichler order of level $Nr$, a prime $\ell\notin\{r,\bar r\}$, a unit $s$ of $\mathbb{H}[\mathbb{Q},a_1,b_1]$ with $\mathrm{nrd}(s)=\ell$, and a finite-adelic unit $s_f$ whose component at each $v\nmid r$ is $s\otimes1$ and whose components above $r$ are $1$, such that the diagonal image of $\ell$ times $s_f^{-1}$ lies in $\operatorname{levelHeckeUSet}\Lambda_1(\operatorname{meetOrder}R_1\,n_1)\,\ell$ when $\ell\mid N$ and in $\operatorname{primeHeckeSet}(\operatorname{meetOrder}R_1\,n_1)\,\ell$ otherwise. Finally let $m\in\mathbb{N}$ and $x_b\in R_2$ with $x_b=r^{m}\,\overline{s}$. The conclusion: for every scheme $T$, every $t:T\to\operatorname{Spec}k_0$ and every section $P$ of $A_0.f$ over $t$, if $P$ factors through $A_0.\mathrm{lev}$, if $\ell P$ is the identity section for $A_0.L$, and if $P$ followed by $\hat e(x_b)$ is the identity section, then $P$ itself is the identity section.
--
--   This is the statement that the kernel of the endomorphism $\hat e(r^m\bar s)$ meets the $\ell$-torsion of the level subscheme trivially, for $\ell$ a prime away from $r$ and $\bar r$ carrying a Hecke element of reduced norm $\ell$. It is used in the construction of the Hecke-operator dictionary on fake elliptic curves in characteristic $r$, via `exists_heckeDictionary_star_and_comp_eq_of_endomorphismDictionary_endIsoFull`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_forall_factorsThrough_lev_nsmulPt_eq_one_mapPt_eq_one_imp_eq_one_of_levelHeckeUSet_of_endIsoFull.lean

import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_ReducedNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.forall_factorsThrough_lev_nsmulPt_eq_one_mapPt_eq_one_imp_eq_one_of_levelHeckeUSet_of_endIsoFull
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N)
    (hN : Squarefree N)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] [CharP k₀ r] (A₀ : FakeEllipticCurve Λ N k₀)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)

    (R₂ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₂ : R₂ ≤ R₁) (hR₂o : IsOrder R₂)
    (hR₂r : ∀ x : ↥R₁, ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • (x : ℍ[ℚ, a₁, b₁]) ∈ R₂)
    (ê : ↥R₂ → (A₀.A ⟶ A₀.A)) (hê : ∀ x, ê x ≫ A₀.f = A₀.f)
    (hE5a : ∀ x : ↥R₂,
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
          mapPt (ê x) (hê x) (A₀.L.mul t P Q) = A₀.L.mul t (mapPt (ê x) (hê x) P) (mapPt (ê x) (hê x) Q)) ∧
      (∀ m : ↥Λ, A₀.act m ≫ ê x = ê x ≫ A₀.act m) ∧
      FakeEllipticCurve.PreservesLevel A₀ A₀ (ê x) (hê x))
    (hE5one : ∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R₂, ê ⟨1, h⟩ = 𝟙 A₀.A)
    (hE5mul : ∀ (x y : ↥R₂) (h : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R₂),
      ê ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ê y ≫ ê x)
    (hE5int : ∀ (m : ℤ) (h : ((m : ℚ) : ℍ[ℚ, a₁, b₁]) ∈ R₂), ê ⟨((m : ℚ) : ℍ[ℚ, a₁, b₁]), h⟩ = A₀.act ⟨((m : ℤ) : ℚ), hΛℤ m⟩)

    (hE5g : ∀ z : ↥R₂, star (z : ℍ[ℚ, a₁, b₁]) ∈ R₂)

    (Λ₁s : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁s : IsMaximalOrder Λ₁s) (hR₁Λ₁s : R₁ ≤ Λ₁s) (htwin : Λ₁ ⊓ Λ₁s = R₁)
    (R₂' : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₂' : R₂' ≤ Λ₁s) (hR₂'o : IsOrder R₂')
    (hR₂'r : ∀ z : ↥Λ₁s, ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • (z : ℍ[ℚ, a₁, b₁]) ∈ R₂') (hR₂R₂' : R₂ ≤ R₂')
    (ê' : ↥R₂' → (A₀.A ⟶ A₀.A)) (hê' : ∀ z, ê' z ≫ A₀.f = A₀.f)
    (hE6a : ∀ z : ↥R₂',
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
          mapPt (ê' z) (hê' z) (A₀.L.mul t P Q) = A₀.L.mul t (mapPt (ê' z) (hê' z) P) (mapPt (ê' z) (hê' z) Q)) ∧
      (∀ m : ↥Λ, A₀.act m ≫ ê' z = ê' z ≫ A₀.act m))
    (hE6one : ∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R₂', ê' ⟨1, h⟩ = 𝟙 A₀.A)
    (hE6mul : ∀ (z y : ↥R₂') (h : (z : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R₂'),
      ê' ⟨(z : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ê' y ≫ ê' z)
    (hE6int : ∀ (m : ℤ) (h : ((m : ℚ) : ℍ[ℚ, a₁, b₁]) ∈ R₂'), ê' ⟨((m : ℚ) : ℍ[ℚ, a₁, b₁]), h⟩ = A₀.act ⟨((m : ℤ) : ℚ), hΛℤ m⟩)
    (hE6c : ∀ (z y : ↥R₂') (nz : ℤ), (y : ℍ[ℚ, a₁, b₁]) = star (z : ℍ[ℚ, a₁, b₁]) → nrd (z : ℍ[ℚ, a₁, b₁]) = (nz : ℚ) →
      ê' y ≫ ê' z = A₀.act ⟨((nz : ℤ) : ℚ), hΛℤ nz⟩)
    (hE6d : ∀ z : ↥R₂, ê' ⟨(z : ℍ[ℚ, a₁, b₁]), hR₂R₂' z.2⟩ = ê z)
    (hE6star : ∀ z : ↥R₂', star (z : ℍ[ℚ, a₁, b₁]) ∈ R₂')
    (hE6inj : ∀ z y : ↥R₂', ê' z = ê' y → z = y)
    (hE6f : ∀ (q : ℕ), q.Prime → q ≠ r → ∀ z : ↥R₂',
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t A₀.f),
          nsmulPt A₀.L t q P = A₀.L.one t → mapPt (ê' z) (hê' z) P = A₀.L.one t) →
      ∃ (K : ℕ) (y : ↥Λ₁s), ((r ^ K : ℕ) : ℚ) • (z : ℍ[ℚ, a₁, b₁]) = (q : ℚ) • (y : ℍ[ℚ, a₁, b₁]))

    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ r)
    (hS₁ : IsEichlerOrder (meetOrder R₁ n₁) (N * r))
    (ℓ : HeckeTower.AwayPrime r rbar) (s : (ℍ[ℚ, a₁, b₁])ˣ)
    (sf : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs :
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * sf⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₁ (meetOrder R₁ n₁) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ)) ∧
      nrd (s : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ))

    (m : ℕ) (xb : ↥R₂) (hxb : (xb : ℍ[ℚ, a₁, b₁]) = ((r ^ m : ℕ) : ℚ) • star ((s : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) :
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t A₀.f),
      FactorsThrough A₀.lev P → nsmulPt A₀.L t (ℓ.1 : ℕ) P = A₀.L.one t → mapPt (ê xb) (hê xb) P = A₀.L.one t → P = A₀.L.one t := by sorry
