-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_corr_of_isPullbackVia_of_isPullbackVia_of_squareZero
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_corr_of_isPullbackVia_of_isPullbackVia_of_squareZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/b110d297-cfb4-59b6-80b8-bb4d02d6b1c4
-- title:
--   Rigidity of rigidification correspondences along square-zero thickenings
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ containing the image of every integer (hypothesis $h\Lambda\mathbb{Z}$), a natural number $N$, a natural number $r$, a commutative ring $\mathcal{O}$ with an element $\pi$, an $\mathcal{O}$-algebra $O^{nr}$, and a fake elliptic curve $A_0$ for $(\Lambda,N)$ over $O^{nr}/(\pi)$ — that is, an abelian scheme of relative dimension $2$ with commutative relative group law, an action of $\Lambda$ satisfying the trace condition, and level-$N$ data. Let $p : B \to B_0$ be a surjective homomorphism of $\mathcal{O}$-algebras whose kernel is square-zero (any two elements killed by $p$ have product $0$), let $\psi : O^{nr} \to B$ be an $\mathcal{O}$-algebra map, and assume $N$ is invertible in $B/(\pi)$. Let $E$ be a fake elliptic curve over $B$, $E_0$ one over $B_0$, and $g : E_0.A \to E.A$ a morphism exhibiting $E_0$ as the base change of $E$ along $p$ in the sense of `FakeEllipticCurve.IsPullbackVia`: the square over $\operatorname{Spec}$ of $p$ is a pullback, and $g$ is compatible with the relative group laws, with the $\Lambda$-actions, and with the level structures. Let $\varrho_1,\varrho_2$ be rigidifications of $E$ relative to $\psi$ and $A_0$ (each consisting of a fake elliptic curve $E_b$ over $B/(\pi)$ pinned to $E$ by a pullback map $g_b$, a fake elliptic curve $A_b$ over $B/(\pi)$ pinned to $A_0$ by a pullback map $g_A$ along the induced map $O^{nr}/(\pi) \to B/(\pi)$, an exponent $d$, and a level-preserving isogeny pair $\varphi,\varphi'$ of degree $r^d$ between $E_b$ and $A_b$), and let $\varrho_{1,0},\varrho_{2,0}$ be rigidifications of $E_0$ relative to $p \circ \psi$ which are the base changes of $\varrho_1,\varrho_2$ along $p$ and $g$ in the sense of `Rigidification.IsPullbackVia`. Assume the two reduced rigidifications correspond: there are $i_b : \varrho_{1,0}.E_b.A \to \varrho_{2,0}.E_b.A$ compatible with the pinnings $g_b$ and with the structure maps to the base, a comparison $u_A : \varrho_{2,0}.A_b.A \to \varrho_{1,0}.A_b.A$ which is a pullback along the identity ring homomorphism and compatible with the pinnings $g_A$, and exponents $i,j \in \mathbb{N}$ with $i_b$ followed by $\varrho_{2,0}.\varphi$, $u_A$ and the action of the scalar $r^i$ equal to $\varrho_{1,0}.\varphi$ followed by the action of $r^j$. The conclusion asserts data of exactly the same shape for $\varrho_1,\varrho_2$ over $B$: morphisms $i_b$, $u_A$ with the analogous compatibilities and exponents $i,j$ (again existentially quantified) satisfying the same identity in $\varrho_1.A_b$.
--
--   This is the rigidity of homomorphisms of abelian schemes along a nilpotent (here square-zero) thickening of the base, transported to rigidifications of fake elliptic curves: correspondence of two rigidifications descends from the quotient $B_0$ to $B$, the comparison morphisms upstairs being pinned by the maps to $E$ and to $A_0$. It is used in the Čerednik–Drinfeld analysis of the $p$-adic uniformisation of quaternionic (fake elliptic) moduli, in the identification of the invariant attached to a rigidified point along square-zero deformations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_corr_of_isPullbackVia_of_isPullbackVia_of_squareZero.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_corr_of_isPullbackVia_of_isPullbackVia_of_squareZero
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}

    {B : Type} [CommRing B] [Algebra 𝒪 B] {B₀ : Type} [CommRing B₀] [Algebra 𝒪 B₀] (p : B →ₐ[𝒪] B₀)
    (hp : Function.Surjective p) (hp2 : ∀ s t : B, p s = 0 → p t = 0 → s * t = 0)
    (ψ : Onr →ₐ[𝒪] B)

    (hNb : IsUnit ((N : ℕ) : B ⧸ Ideal.span {algebraMap 𝒪 B π}))

    (E : FakeEllipticCurve Λ N B) (E₀ : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (p : B →+* B₀) E E₀ g)

    (ϱ₁ ϱ₂ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (ϱ₁₀ ϱ₂₀ : FakeEllipticCurve.Rigidification r π A₀ (p.comp ψ) E₀)
    (h₁ : FakeEllipticCurve.Rigidification.IsPullbackVia p g hg ϱ₁ ϱ₁₀)
    (h₂ : FakeEllipticCurve.Rigidification.IsPullbackVia p g hg ϱ₂ ϱ₂₀)

    (h₀ : ∃ (ib : ϱ₁₀.Eb.A ⟶ ϱ₂₀.Eb.A) (_ : ib ≫ ϱ₂₀.gb = ϱ₁₀.gb) (_ : ib ≫ ϱ₂₀.Eb.f = ϱ₁₀.Eb.f)
      (uA : ϱ₂₀.Ab.A ⟶ ϱ₁₀.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ₁₀.Ab ϱ₂₀.Ab uA) (_ : uA ≫ ϱ₁₀.gA = ϱ₂₀.gA)
      (i j : ℕ),
      ib ≫ ϱ₂₀.φ ≫ uA ≫ ϱ₁₀.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ₁₀.φ ≫ ϱ₁₀.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
    ∃ (ib : ϱ₁.Eb.A ⟶ ϱ₂.Eb.A) (_ : ib ≫ ϱ₂.gb = ϱ₁.gb) (_ : ib ≫ ϱ₂.Eb.f = ϱ₁.Eb.f)
      (uA : ϱ₂.Ab.A ⟶ ϱ₁.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ₁.Ab ϱ₂.Ab uA) (_ : uA ≫ ϱ₁.gA = ϱ₂.gA)
      (i j : ℕ),
      ib ≫ ϱ₂.φ ≫ uA ≫ ϱ₁.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ₁.φ ≫ ϱ₁.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by sorry
