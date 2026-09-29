-- Prove2me | Theorems.Thm_CuspForm_exists_eigenform_qCoeff_congr_of_heckeT_sub_mem
-- name    : CuspForm.exists_eigenform_qCoeff_congr_of_heckeT_sub_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/ee0046d5-fe0d-5aca-aa32-fad04446d41c
-- title:
--   Deligne–Serre lifting: eigenform congruent to a mod-𝔪 eigensystem
-- statement:
--   Let $p$ be a prime, let $M$ be a nonzero natural number divisible by $p$, let $w$ be an integer and let $S$ be any set of natural numbers. Let $\mathfrak{m}$ be a maximal ideal of the integral closure $\bar{\mathbb{Z}}$ of $\mathbb{Z}$ in $\mathbb{C}$ containing $p$, and let $K$ be an intermediate field of $\mathbb{Q} \subseteq \mathbb{C}$ of finite degree over $\mathbb{Q}$. Let $F$ be a cusp form of weight $w$ for $\Gamma_0(M)$ whose $q$-expansion coefficients $a_n(F) =$ `qCoeff F n` (the coefficients of the width-$1$ $q$-expansion) all lie in $K$ and are all images of elements of $\bar{\mathbb{Z}}$, and suppose some $a_n(F)$ is the image of an element of $\bar{\mathbb{Z}}$ lying outside $\mathfrak{m}$. Let $c_T : \mathbb{N} \to \mathbb{Z}$ and $c_U \in \mathbb{Z}$ be given, and assume the coefficientwise congruences: for every prime $\ell \notin S$ with $\ell \nmid M$, every $n$ and all $x, x' \in \bar{\mathbb{Z}}$ with $x = a_n(T_\ell F)$ and $x' = a_n(F)$ one has $x - c_T(\ell)x' \in \mathfrak{m}$; and for every $n$ and all $x, x' \in \bar{\mathbb{Z}}$ with $x = a_n(U_p F)$ and $x' = a_n(F)$ one has $x - c_U x' \in \mathfrak{m}$. Here $T_\ell$ is `heckeTLin`, the endomorphism of $S_w(\Gamma_0(M))$ induced by $f \mapsto \sum_{j<\ell} f\mid_w \mathrm{heckeMatrix}\,\ell\,j + f\mid_w \mathrm{heckeDiagMatrix}\,\ell$, and $U_p$ is `heckeULin`, induced by $f \mapsto \sum_{j<p} f\mid_w \mathrm{heckeMatrix}\,p\,j$. The conclusion asserts the existence of a maximal ideal $\mathfrak{m}'$ of $\bar{\mathbb{Z}}$ containing $p$ and a cusp form $f$ of weight $w$ for $\Gamma_0(M)$ such that: (i) each $a_n(f)$ is $\mathfrak{m}'$-integral, in the sense that there are $x, y \in \bar{\mathbb{Z}}$ with $y \notin \mathfrak{m}'$ and $x = y\,a_n(f)$; (ii) for some $n$ such $x, y$ may be chosen with in addition $x \notin \mathfrak{m}'$; (iii) for every prime $\ell \notin S$ with $\ell \nmid M$ there is $\lambda \in \bar{\mathbb{Z}}$ with $\lambda - c_T(\ell) \in \mathfrak{m}'$ and $T_\ell f = \lambda f$; and (iv) there is $\alpha \in \bar{\mathbb{Z}}$ with $\alpha - c_U \in \mathfrak{m}'$ and $U_p f = \alpha f$.
--
--   This is the lifting lemma of Deligne–Serre, formulated for the algebraic integers in $\mathbb{C}$ and without assuming any integral structure or finiteness for the weight-$w$ Hecke algebra: a cusp form whose coefficients are algebraic integers, not all in $\mathfrak{m}$, and which is an eigenvector of the Hecke operators modulo $\mathfrak{m}$ with integer eigenvalues, is replaced by a genuine eigenform with eigenvalues congruent to those integers modulo a maximal ideal $\mathfrak{m}'$ above $p$. It is used in the passage from a mod $p$ system of eigenvalues to a characteristic-zero eigenform, and is cited by [`WeierstrassCurve.exists_ideal_heckeAlgebra_ordCompl_of_isNewform_sq_dvd`](thm.html#WeierstrassCurve.exists_ideal_heckeAlgebra_ordCompl_of_isNewform_sq_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_eigenform_qCoeff_congr_of_heckeT_sub_mem.lean

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CuspForm ModularFormClass

theorem CuspForm.exists_eigenform_qCoeff_congr_of_heckeT_sub_mem (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (w : ℤ) (S : Set ℕ)
    (𝔪 : Ideal (integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (F : CuspForm (CongruenceSubgroup.Gamma0 M) w) (hFK : ∀ n : ℕ, qCoeff F n ∈ K)
    (hFint : ∀ n : ℕ, ∃ x : integralClosure ℤ ℂ, (x : ℂ) = qCoeff F n)
    (hFne : ∃ (n : ℕ) (x : integralClosure ℤ ℂ), (x : ℂ) = qCoeff F n ∧ x ∉ 𝔪)
    (cT : ℕ → ℤ) (cU : ℤ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M) (n : ℕ) (x x' : integralClosure ℤ ℂ),
      (x : ℂ) = qCoeff (heckeTLin w hℓ hℓM F) n → (x' : ℂ) = qCoeff F n → x - cT ℓ * x' ∈ 𝔪)
    (hU : ∀ (n : ℕ) (x x' : integralClosure ℤ ℂ),
      (x : ℂ) = qCoeff (heckeULin w hpM F) n → (x' : ℂ) = qCoeff F n → x - cU * x' ∈ 𝔪) :
    ∃ 𝔪' : Ideal (integralClosure ℤ ℂ), 𝔪'.IsMaximal ∧ (p : integralClosure ℤ ℂ) ∈ 𝔪' ∧
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 M) w,
      (∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪' ∧ (x : ℂ) = y * qCoeff f n) ∧
      (∃ (n : ℕ) (x y : integralClosure ℤ ℂ), y ∉ 𝔪' ∧ (x : ℂ) = y * qCoeff f n ∧ x ∉ 𝔪') ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M),
        ∃ lam : integralClosure ℤ ℂ, lam - cT ℓ ∈ 𝔪' ∧ heckeTLin w hℓ hℓM f = (lam : ℂ) • f) ∧
      (∃ α : integralClosure ℤ ℂ, α - cU ∈ 𝔪' ∧ heckeULin w hpM f = (α : ℂ) • f) := by sorry
