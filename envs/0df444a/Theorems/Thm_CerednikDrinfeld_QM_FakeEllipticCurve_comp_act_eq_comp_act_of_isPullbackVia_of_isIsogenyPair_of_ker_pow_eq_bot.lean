-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_comp_act_eq_comp_act_of_isPullbackVia_of_isIsogenyPair_of_ker_pow_eq_bot
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.comp_act_eq_comp_act_of_isPullbackVia_of_isIsogenyPair_of_ker_pow_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/5cd69233-84bd-5c07-b5fa-690facc6cac0
-- title:
--   Rigidity of isogeny pairs along a nilpotent thickening
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ containing the image of every integer (hypothesis `hΛℤ`), a natural number $N$, and a natural number $r$. Let $f_{00}\colon \bar B \to \bar B_0$ be a surjective homomorphism of commutative rings whose kernel satisfies $(\ker f_{00})^n = 0$ for some $n$. Let $E_b$ and $A_b$ be fake elliptic curves over $\bar B$ and $E_{0b}$ one over $\bar B_0$ (each consisting of a scheme over the base equipped with a commutative relative group law, an abelian-scheme property bundle, two-dimensional fibres, a $\Lambda$-action by endomorphisms over the base that is additive and multiplicative and satisfies the trace condition, and level data). Let $u\colon E_{0b}.A \to E_b.A$ satisfy `IsPullbackVia f₀₀ Eb E₀b u`, i.e. the square formed by $u$, the two structure morphisms and $\mathrm{Spec}(f_{00})$ is cartesian, $u$ carries the group law of $E_{0b}$ to that of $E_b$ on points, intertwines the $\Lambda$-actions ($E_{0b}.\mathrm{act}(x)$ followed by $u$ equals $u$ followed by $E_b.\mathrm{act}(x)$), and sends points factoring through the level scheme of $E_{0b}$ to points factoring through that of $E_b$. Let $d_1,d_2,i,j$ be natural numbers and $\varphi_1,\varphi_2\colon E_b.A \to A_b.A$, $\varphi_1',\varphi_2'\colon A_b.A \to E_b.A$ be such that $(\varphi_1,\varphi_1')$ and $(\varphi_2,\varphi_2')$ are isogeny pairs of degrees $r^{d_1}$ and $r^{d_2}$: each of the four morphisms lies over the base, preserves the relative group laws on points, commutes with the $\Lambda$-actions, and, whenever the degree lies in $\Lambda$, the two composites are the actions of that degree on $E_b$ and on $A_b$. Then, writing $[r^i]$ for $A_b.\mathrm{act}$ at the element of $\Lambda$ given by the integer $r^i$, if $u$ followed by $\varphi_1$ followed by $[r^i]$ equals $u$ followed by $\varphi_2$ followed by $[r^j]$, then already $\varphi_1$ followed by $[r^i]$ equals $\varphi_2$ followed by $[r^j]$.
--
--   This is the rigidity of homomorphisms of abelian schemes along a nilpotent thickening of the base, in the form needed for fake elliptic curves with quaternionic multiplication: two isogenies that agree up to $r$-power scalars after base change along $f_{00}$ agree already over $\bar B$. It is used in the rigidification comparison for fake elliptic curves and in the proof that the functor classifying isogeny pairs is formally unramified, via the general group-law rigidity statement [`GoodReductionJacobian.RelativeGroupLaw.eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker`](thm.html#GoodReductionJacobian.RelativeGroupLaw.eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_comp_act_eq_comp_act_of_isPullbackVia_of_isIsogenyPair_of_ker_pow_eq_bot.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.comp_act_eq_comp_act_of_isPullbackVia_of_isIsogenyPair_of_ker_pow_eq_bot
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (r : ℕ)
    (Bb B₀b : Type) [CommRing Bb] [CommRing B₀b] (f₀₀ : Bb →+* B₀b) (hf : Function.Surjective f₀₀)
    (hnil : ∃ n : ℕ, RingHom.ker f₀₀ ^ n = ⊥)
    (Eb : FakeEllipticCurve Λ N Bb) (E₀b : FakeEllipticCurve Λ N B₀b) (Ab : FakeEllipticCurve Λ N Bb)
    (u : E₀b.A ⟶ Eb.A) (hu : FakeEllipticCurve.IsPullbackVia f₀₀ Eb E₀b u)
    (d₁ d₂ : ℕ) (φ₁ φ₂ : Eb.A ⟶ Ab.A) (φ₁' φ₂' : Ab.A ⟶ Eb.A)
    (h₁ : FakeEllipticCurve.IsIsogenyPair (r ^ d₁) Eb Ab φ₁ φ₁') (h₂ : FakeEllipticCurve.IsIsogenyPair (r ^ d₂) Eb Ab φ₂ φ₂')
    (i j : ℕ)
    (hagree : u ≫ φ₁ ≫ Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = u ≫ φ₂ ≫ Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
    φ₁ ≫ Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = φ₂ ≫ Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by sorry
