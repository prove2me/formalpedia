-- Prove2me | Theorems.Thm_CohCarrier_exists_dirichletCharacter_pair_of_not_mem_parabolicHoms_of_heckeT_eq_smul
-- name    : CohCarrier.exists_dirichletCharacter_pair_of_not_mem_parabolicHoms_of_heckeT_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/79e48f97-413a-5a0b-96b7-40fbad694ca8
-- title:
--   Non-parabolic Hecke eigenclasses in H¹(Γ_H(M),ℂ) are Eisenstein
-- statement:
--   Let $M\ge 1$, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$ and let $S$ be an arbitrary set of natural numbers. Write $\Gamma_H(M)$ for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, namely the image of those $\gamma\in\Gamma_0(M)$ whose lower-right entry lies in $H$ modulo $M$, and let $\varphi$ be an element of [`CohCarrier.H1 M H ℂ`](def/CohCarrier_Level.html#L162), that is an additive homomorphism $\mathrm{Additive}\,\Gamma_H(M)\to\mathbb{C}$ (a character of $\Gamma_H(M)$ with values in $\mathbb{C}$). Assume $\varphi$ does not lie in [`ModularCurve.Period.parabolicHoms`](def/ModularCurve_PeriodMap.html#L62), i.e. there is some $\gamma\in\Gamma_H(M)$ with $(\mathrm{tr}\,\gamma)^2=4$ and $\varphi(\gamma)\ne 0$. Let $a\colon\mathbb{N}\to\mathbb{C}$ and let $e\colon(\mathbb{Z}/M)^\times\to\mathbb{C}^\times$ be a group homomorphism, and suppose that $\varphi$ is an eigenvector: [`CohCarrier.heckeT M H ℓ ℂ`](def/CohCarrier_Level.html#L250) (the transfer to $\Gamma_H(M)$ of $\varphi$ composed with the conjugation homomorphism [`CohCarrier.conjL M H ℓ`](def/CohCarrier_Level.html#L228) from `GammaHUpper M H ℓ`) sends $\varphi$ to $a(\ell)\cdot\varphi$ for every prime $\ell\notin S$ with $\ell\nmid M$, and [`CohCarrier.diamondL M H ℂ u`](def/CohCarrier_Inst.html#L55) (precomposition with conjugation by a chosen element of $\Gamma_0(M)$ of lower-right entry $u$) sends $\varphi$ to $e(u)\cdot\varphi$ for every unit $u$. Then there exist Dirichlet characters $\psi_1,\psi_2$ modulo $M$ with values in $\mathbb{C}$ such that $\psi_1(u)\psi_2(u)=e(u)$ for all $u\in(\mathbb{Z}/M)^\times$ and $a(\ell)=\psi_1(\ell)+\ell\,\psi_2(\ell)$ for every prime $\ell\notin S$ with $\ell\nmid M$. No constraint is placed on $a(n)$ for other $n$.
--
--   This is the statement that the non-parabolic (boundary) part of the first cohomology of $\Gamma_H(M)$ carries only Eisenstein systems of Hecke eigenvalues: a common eigenclass of the $T_\ell$ and the diamond operators which fails to vanish on some element of trace $\pm 2$ has eigenvalues of the shape $\psi_1(\ell)+\ell\psi_2(\ell)$. It is used to extract the Eisenstein alternative in the dichotomy results producing a weight-two eigenform, and hence a Galois representation, from an eigensystem in $H^1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_dirichletCharacter_pair_of_not_mem_parabolicHoms_of_heckeT_eq_smul.lean

import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import Mathlib.NumberTheory.DirichletCharacter.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.exists_dirichletCharacter_pair_of_not_mem_parabolicHoms_of_heckeT_eq_smul
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (φ : CohCarrier.H1 M H ℂ)
    (hφpar : φ ∉ ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)
    (a : ℕ → ℂ) (e : (ZMod M)ˣ →* ℂˣ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ M →
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT M H ℓ ℂ φ) = a ℓ • φ)
    (hD : ∀ u : (ZMod M)ˣ, CohCarrier.diamondL M H ℂ u φ = (e u : ℂ) • φ) :
    ∃ ψ₁ ψ₂ : DirichletCharacter ℂ M,
      (∀ u : (ZMod M)ˣ, ψ₁ (u : ZMod M) * ψ₂ (u : ZMod M) = e u) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ M →
        a ℓ = ψ₁ (ℓ : ZMod M) + (ℓ : ℂ) * ψ₂ (ℓ : ZMod M)) := by sorry
