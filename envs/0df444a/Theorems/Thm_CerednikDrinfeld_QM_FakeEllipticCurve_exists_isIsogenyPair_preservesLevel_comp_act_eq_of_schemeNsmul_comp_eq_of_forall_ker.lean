-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isIsogenyPair_preservesLevel_comp_act_eq_of_schemeNsmul_comp_eq_of_forall_ker
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isIsogenyPair_preservesLevel_comp_act_eq_of_schemeNsmul_comp_eq_of_forall_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/ec7d3aef-64c2-51a7-8c30-729b773e2076
-- title:
--   Dividing an isogeny by [r^{d-k}] on fake elliptic curves
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ containing the image of every integer, a natural number $N$, a prime $r$ with $r \nmid N$, and a Noetherian commutative ring $S$; let $E$ and $A$ be fake elliptic curves over $S$ of level $N$ with $\Lambda$-action. Assume given $\varphi : E.A \to A.A$ over $\operatorname{Spec} S$ (that is, $\varphi$ followed by $A.f$ equals $E.f$), $\varphi' : A.A \to E.A$ and $d \in \mathbb{N}$ such that $(\varphi,\varphi')$ is an isogeny pair of degree $r^{d}$: both maps lie over $\operatorname{Spec} S$, both are homomorphisms for the relative group laws on $T$-points, both commute with the actions of all $x \in \Lambda$, and, whenever the image of $r^{d}$ lies in $\Lambda$, $\varphi$ followed by $\varphi'$ is $E.\mathrm{act}(r^{d})$ and $\varphi'$ followed by $\varphi$ is $A.\mathrm{act}(r^{d})$. Assume also that $\varphi$ preserves level, i.e. for every $t : T \to \operatorname{Spec} S$ and every point $P$ of $E$ over $t$ factoring through $E.\mathrm{lev}$, the point $P$ followed by $\varphi$ factors through $A.\mathrm{lev}$. Let $k \le d$ and let $\psi' : A.A \to E.A$ satisfy: multiplication by $r^{k}$ on $A$ (the morphism $A.L.\mathrm{schemeNsmul}\,(r^{k})$) followed by $\psi'$ equals $\varphi'$; $\psi'$ lies over $\operatorname{Spec} S$; and $\psi'$ carries the group law of $A$ on $T$-points to that of $E$. Let $h \in \mathbb{N}$ be such that the kernel of $\psi'$ is killed by $r^{h}$ on points: for every $t : T \to \operatorname{Spec} S$ and every point $P$ of $A$ over $t$ with $P$ followed by $\psi'$ equal to the identity section of $E$, one has $r^{h}\cdot P =$ the identity section of $A$. The conclusion is that there exists $\gamma : E.A \to A.A$ over $\operatorname{Spec} S$ such that $(\gamma,\psi')$ is an isogeny pair of degree $r^{h}$, $\gamma$ preserves level, and $\gamma$ followed by $A.\mathrm{act}$ of the integer $r^{d-k}$ equals $\varphi$ followed by $A.\mathrm{act}$ of the integer $r^{h}$.
--
--   This is the construction of the complementary (dual) leg after dividing an isogeny by a power of $r$: given that $\varphi'$ factors as $[r^{k}]$ followed by $\psi'$ and that $\ker \psi'$ is killed by $r^{h}$, a $\Lambda$-equivariant, level-preserving $\gamma$ is produced with $(\gamma,\psi')$ an isogeny pair of degree $r^{h}$ and with $[r^{d-k}] \circ \gamma = [r^{h}] \circ \varphi$. It is used in the re-rigidification lemmas for fake elliptic curves over Artinian and over local rings, where the divided leg replaces the original isogeny pair.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isIsogenyPair_preservesLevel_comp_act_eq_of_schemeNsmul_comp_eq_of_forall_ker.lean

import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isIsogenyPair_preservesLevel_comp_act_eq_of_schemeNsmul_comp_eq_of_forall_ker
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {r : ℕ} [Fact r.Prime] (hrN : ¬ r ∣ N)
    {S : Type} [CommRing S] [IsNoetherianRing S]
    (E A : FakeEllipticCurve Λ N S)

    (φ : E.A ⟶ A.A) (hφ : φ ≫ A.f = E.f) (φ' : A.A ⟶ E.A) (d : ℕ)
    (hpair : FakeEllipticCurve.IsIsogenyPair (r ^ d) E A φ φ')
    (hφlev : FakeEllipticCurve.PreservesLevel E A φ hφ)

    (k : ℕ) (hkd : k ≤ d) (ψ' : A.A ⟶ E.A)
    (hfac : A.L.schemeNsmul (r ^ k) ≫ ψ' = φ')
    (hψ'f : ψ' ≫ E.f = A.f)
    (hψ'hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A.f),
      (A.L.mul t P Q).1 ≫ ψ' =
        (E.L.mul t ⟨P.1 ≫ ψ', by rw [Category.assoc, hψ'f]; exact P.2⟩
          ⟨Q.1 ≫ ψ', by rw [Category.assoc, hψ'f]; exact Q.2⟩).1)

    (h : ℕ)
    (hker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t A.f),
      P.1 ≫ ψ' = (E.L.one t).1 → nsmulPt A.L t (r ^ h) P = A.L.one t) :
    ∃ (γ : E.A ⟶ A.A) (hγ : γ ≫ A.f = E.f),
      FakeEllipticCurve.IsIsogenyPair (r ^ h) E A γ ψ' ∧
      FakeEllipticCurve.PreservesLevel E A γ hγ ∧
      γ ≫ A.act ⟨(((r ^ (d - k) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = φ ≫ A.act ⟨(((r ^ h : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by sorry
