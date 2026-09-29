-- Prove2me | Theorems.Thm_CohCarrier_exists_isEigenformWith_qCoeff_eq_of_mem_parabolicHoms_of_heckeT_eq_smul
-- name    : CohCarrier.exists_isEigenformWith_qCoeff_eq_of_mem_parabolicHoms_of_heckeT_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/c1a89d5f-32e4-5286-bc49-344230d312e6
-- title:
--   Parabolic Hecke eigenclasses on Γ_H(M) come from weight-two eigenforms
-- statement:
--   Let $M\ge 1$, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$, let $S,Q$ be sets of natural numbers with every $q\in Q$ dividing $M$, and let $\Gamma_H(M)$ denote [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the homomorphism $\Gamma_0(M)\to(\mathbb{Z}/M)^\times$ given by reduction of the lower-right entry. Let $\varphi$ be an additive homomorphism $\Gamma_H(M)\to\mathbb{C}$ (an element of [`CohCarrier.H1 M H ℂ`](def/CohCarrier_Level.html#L162)) which is parabolic, i.e. $\varphi(\gamma)=0$ for every $\gamma$ whose matrix trace satisfies $\operatorname{tr}(\gamma)^2=4$, and which is non-zero. Let $a,b\colon\mathbb{N}\to\mathbb{C}$ and let $e\colon(\mathbb{Z}/M)^\times\to\mathbb{C}^\times$ be a character. Assume: $\mathrm{heckeT}_\ell\varphi=a(\ell)\,\varphi$ for every prime $\ell\notin S$ with $\ell\nmid M$; $\mathrm{heckeT}_q\varphi=b(q)\,\varphi$ for every $q\in Q$; and $\mathrm{diamondL}_u\varphi=e(u)\,\varphi$ for every unit $u$. Here $\mathrm{heckeT}_n$ is the transfer, along the inclusion `GammaHUpper M H n` $\le\Gamma_H(M)$, of $\varphi$ precomposed with the conjugation map [`CohCarrier.conjL M H n`](def/CohCarrier_Level.html#L228), and $\mathrm{diamondL}_u$ is precomposition with conjugation by a chosen element of $\Gamma_0(M)$ whose lower-right entry reduces to $u$. The conclusion: there exist a Dirichlet character $\varepsilon$ modulo $M$ with values in $\mathbb{C}$ and a cusp form $h$ of weight $2$ on $\Gamma_1(M)$ such that [`CuspForm.IsEigenformWith ε h`](def/CuspForm_PrimitiveFormGamma1.html#L19) holds (normalisation $a_1(h)=1$, the relations $a_{pn}(h)+\varepsilon(p)\,p\,[p\mid n]\,a_{n/p}(h)=a_p(h)a_n(h)$ for primes $p\nmid M$, the relations $a_{\ell n}(h)=a_\ell(h)a_n(h)$ for primes $\ell\mid M$, and the nebentypus law $h(\gamma\tau)=\varepsilon(\gamma_{11})(\gamma_{10}\tau+\gamma_{11})^2h(\tau)$ for $\gamma\in\Gamma_0(M)$), with $\varepsilon(u)=e(u)$ for all units $u$, with $q$-expansion coefficients $a_\ell(h)=a(\ell)$ for all primes $\ell\notin S$ not dividing $M$, and $a_q(h)=b(q)$ for all $q\in Q$.
--
--   This is the Eichler–Shimura comparison in the form used here: the systems of eigenvalues of the operators $T_\ell$ ($\ell\nmid M$), $U_q$ ($q\mid M$, $q\in Q$) and the diamond operators occurring on non-zero parabolic classes in $\mathrm{Hom}(\Gamma_H(M),\mathbb{C})$ are realised by weight-two cusp forms on $\Gamma_1(M)$ with nebentypus, with the prescribed eigenvalues appearing as $q$-expansion coefficients. It feeds the dichotomy statement [`CohCarrier.OperatorAlgebra.exists_isEigenformWith_qCoeff_eq_or_eisenstein_of_heckeT_eq_smul`](thm.html#CohCarrier.OperatorAlgebra.exists_isEigenformWith_qCoeff_eq_or_eisenstein_of_heckeT_eq_smul), which separates the cuspidal from the Eisenstein eigensystems in the full cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_isEigenformWith_qCoeff_eq_of_mem_parabolicHoms_of_heckeT_eq_smul.lean

import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.exists_isEigenformWith_qCoeff_eq_of_mem_parabolicHoms_of_heckeT_eq_smul
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (Q : Set ℕ) (hQ : ∀ q ∈ Q, q ∣ M)
    (φ : CohCarrier.H1 M H ℂ)
    (hφpar : φ ∈ ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) (hφ0 : φ ≠ 0)
    (a b : ℕ → ℂ) (e : (ZMod M)ˣ →* ℂˣ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ M →
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT M H ℓ ℂ φ) = a ℓ • φ)
    (hU : ∀ (q : ℕ) (hq : q ∈ Q),
      (haveI : NeZero q := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne M) (hQ q hq)⟩;
        CohCarrier.heckeT M H q ℂ φ) = b q • φ)
    (hD : ∀ u : (ZMod M)ˣ, CohCarrier.diamondL M H ℂ u φ = (e u : ℂ) • φ) :
    ∃ (ε : DirichletCharacter ℂ M) (h : CuspForm (CongruenceSubgroup.Gamma1 M) 2),
      CuspForm.IsEigenformWith ε h ∧
      (∀ u : (ZMod M)ˣ, ε (u : ZMod M) = e u) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ M → ModularFormClass.qCoeff h ℓ = a ℓ) ∧
      (∀ q ∈ Q, ModularFormClass.qCoeff h q = b q) := by sorry
