-- Prove2me | Theorems.Thm_CohCarrier_exists_isEigenformWith_of_mem_parabolicHoms_of_heckeT_eq_smul
-- name    : CohCarrier.exists_isEigenformWith_of_mem_parabolicHoms_of_heckeT_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/59b66839-ed51-57ca-a034-4b5ed3d4207f
-- title:
--   Parabolic eigenclasses in H¹(Γ_H(M),ℂ) come from weight-two eigenforms
-- statement:
--   Let $M\ge 1$, let $H$ be a subgroup of $(\mathbb{Z}/M)^{\times}$ and let $S$ be a set of natural numbers. Write $\Gamma_H(M)$ for [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the homomorphism $\Gamma_0(M)\to(\mathbb{Z}/M)^{\times}$ recording the lower-right entry modulo $M$, and let [`CohCarrier.H1 M H ℂ`](def/CohCarrier_Level.html#L162) be the space of homomorphisms $\varphi\colon\Gamma_H(M)\to\mathbb{C}$. Let $\varphi$ be such a homomorphism which is parabolic, i.e. $\varphi(\gamma)=0$ for every $\gamma\in\Gamma_H(M)$ with $(\operatorname{tr}\gamma)^2=4$, and $\varphi\neq 0$. Let $a\colon\mathbb{N}\to\mathbb{C}$ be a function and $e\colon(\mathbb{Z}/M)^{\times}\to\mathbb{C}^{\times}$ a group homomorphism. Assume that for every prime $\ell\notin S$ with $\ell\nmid M$ one has [`CohCarrier.heckeT M H ℓ ℂ`](def/CohCarrier_Level.html#L250) $\varphi=a_\ell\,\varphi$, where `heckeT` is the transfer from `GammaHUpper M H ℓ` to $\Gamma_H(M)$ of $\varphi$ precomposed with the conjugation map `conjL M H ℓ`; and that for every $u\in(\mathbb{Z}/M)^{\times}$ one has [`CohCarrier.diamondL M H ℂ u`](def/CohCarrier_Inst.html#L55) $\varphi=e(u)\,\varphi$, where `diamondL` is precomposition with conjugation by a chosen element of $\Gamma_0(M)$ whose lower-right entry reduces to $u$. Then there exist a Dirichlet character $\varepsilon$ modulo $M$ with values in $\mathbb{C}$ and a cusp form $h$ of weight $2$ on $\Gamma_1(M)$ such that: $h$ satisfies [`CuspForm.IsEigenformWith ε h`](def/CuspForm_PrimitiveFormGamma1.html#L19), that is, its $q$-expansion coefficients (taken at width $1$) satisfy $a_1(h)=1$, the relation $a_{pn}(h)+\varepsilon(p)p^{\,2-1}\,[p\mid n]\,a_{n/p}(h)=a_p(h)a_n(h)$ for all primes $p\nmid M$ and all $n$, the relation $a_{\ell n}(h)=a_\ell(h)a_n(h)$ for all primes $\ell\mid M$ and all $n$, and the nebentypus transformation $h(\gamma\tau)=\varepsilon(d_\gamma)(c_\gamma\tau+d_\gamma)^2h(\tau)$ for all $\gamma\in\Gamma_0(M)$; moreover $\varepsilon(u)=e(u)$ for every $u\in(\mathbb{Z}/M)^{\times}$, and $a_\ell(h)=a_\ell$ for every prime $\ell\notin S$ with $\ell\nmid M$. Nothing is asserted about the coefficients of $h$ at primes in $S$ or dividing $M$.
--
--   This is the Eichler–Shimura comparison for $\Gamma_H(M)$ in eigenvalue form: a non-zero parabolic class in $\mathrm{Hom}(\Gamma_H(M),\mathbb{C})$ which is a simultaneous eigenvector for the Hecke operators $T_\ell$ outside $S\cup\{\ell:\ell\mid M\}$ and for all diamond operators has the same eigenvalue system as a normalised weight-two eigenform on $\Gamma_1(M)$ with nebentypus. It is the bridge from cohomological eigenvalue systems to classical eigenforms, and is used in the project where eigenvalue systems produced by Galois-theoretic and Hecke-algebra arguments must be realised by cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_isEigenformWith_of_mem_parabolicHoms_of_heckeT_eq_smul.lean

import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.exists_isEigenformWith_of_mem_parabolicHoms_of_heckeT_eq_smul
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (φ : CohCarrier.H1 M H ℂ)
    (hφpar : φ ∈ ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) (hφ0 : φ ≠ 0)
    (a : ℕ → ℂ) (e : (ZMod M)ˣ →* ℂˣ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ M →
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT M H ℓ ℂ φ) = a ℓ • φ)
    (hD : ∀ u : (ZMod M)ˣ, CohCarrier.diamondL M H ℂ u φ = (e u : ℂ) • φ) :
    ∃ (ε : DirichletCharacter ℂ M) (h : CuspForm (CongruenceSubgroup.Gamma1 M) 2),
      CuspForm.IsEigenformWith ε h ∧
      (∀ u : (ZMod M)ˣ, ε (u : ZMod M) = e u) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ M → ModularFormClass.qCoeff h ℓ = a ℓ) := by sorry
