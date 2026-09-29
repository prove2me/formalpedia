-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_equiv_addEquiv_mk_eq_and_smul_of_ringEquiv
-- name    : AlgebraicCurve.Pic0.exists_equiv_addEquiv_mk_eq_and_smul_of_ringEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/d6ef579f-81f4-5053-9fd1-698146df087e
-- title:
--   Equivariant transport of Pic⁰ along a field isomorphism
-- statement:
--   Let $K$, $K'$, $F$, $F'$ be fields with $F$ a $K$-algebra and $F'$ a $K'$-algebra, let $e : K \simeq K'$ be a ring isomorphism and $\varphi : F \simeq F'$ a ring isomorphism with $\varphi(\iota_K(a)) = \iota_{K'}(e\,a)$ for all $a \in K$, where $\iota$ denotes the structure maps. Here a place of $F/K$ is a valuation subring $\mathcal{O} \subseteq F$ containing the image of $K$, different from $F$, and a principal ideal ring; a divisor is a finitely supported $\mathbb{Z}$-valued function on places, its degree is $\sum_v D(v)\,\deg v$, and $\mathrm{Pic}^0(F/K)$ is the quotient of the group of degree-zero divisors by its subgroup of principal divisors, i.e. those of the form $v \mapsto \mathrm{ord}_v(f)$ with $f \in F^{\times}$. The assertion is that there exist a bijection $\Phi$ between the places of $F/K$ and those of $F'/K'$ and an isomorphism of additive groups $\Psi : \mathrm{Pic}^0(F/K) \simeq \mathrm{Pic}^0(F'/K')$ such that: (i) for every place $v$, the valuation subring of $\Phi v$ is the preimage of that of $v$ under $\varphi^{-1}$; (ii) for every degree-zero divisor $D$, the pushforward $\Phi_* D$ obtained by transporting the support along $\Phi$ again has degree zero, and $\Psi$ sends the class of $D$ to the class of $\Phi_* D$; and (iii) for all $\sigma \in \mathrm{Aut}(F/K)$ and $\sigma' \in \mathrm{Aut}(F'/K')$ with $\varphi \circ \sigma = \sigma' \circ \varphi$ pointwise on $F$, one has $\Psi(\sigma \cdot x) = \sigma' \cdot \Psi(x)$ for every $x \in \mathrm{Pic}^0(F/K)$, for the actions of the automorphism groups on the respective degree-zero class groups. Beyond its effect on valuation subrings, no further property of $\Phi$ is asserted.
--
--   This is transport of structure for the degree-zero divisor class group of a function field along an isomorphism of the field together with an isomorphism of its field of constants: the induced pushforward on places preserves degrees and principal divisors and so descends to $\mathrm{Pic}^0$, compatibly with automorphism actions. It is used in the comparison of Tate modules of the Drinfeld curve over two isomorphic algebraically closed constant fields, via [`DrinfeldCurve.exists_linearEquiv_tateProd_comp_tateProdRep_eq_of_algEquiv`](thm.html#DrinfeldCurve.exists_linearEquiv_tateProd_comp_tateProdRep_eq_of_algEquiv), and rests on the corresponding transport statement for places, [`AlgebraicCurve.Place.exists_equiv_comap_eq_and_ord_eq_and_deg_eq_of_ringEquiv`](thm.html#AlgebraicCurve.Place.exists_equiv_comap_eq_and_ord_eq_and_deg_eq_of_ringEquiv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_equiv_addEquiv_mk_eq_and_smul_of_ringEquiv.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_JZeroTateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.exists_equiv_addEquiv_mk_eq_and_smul_of_ringEquiv
    {K K' F F' : Type} [Field K] [Field K'] [Field F] [Field F'] [Algebra K F] [Algebra K' F']
    (e : K ≃+* K') (φ : F ≃+* F') (hφ : ∀ a : K, φ (algebraMap K F a) = algebraMap K' F' (e a)) :
    ∃ (Φ : Place K F ≃ Place K' F') (Ψ : Pic0 K F ≃+ Pic0 K' F'),
      (∀ v : Place K F, (Φ v).toValuationSubring = v.toValuationSubring.comap φ.symm.toRingHom) ∧
      (∀ D : Divisor.degZero (K := K) (F := F),
        ∃ hD : Finsupp.mapDomain Φ (D : Divisor K F) ∈ Divisor.degZero (K := K') (F := F'),
          Ψ (Pic0.mk D) = Pic0.mk ⟨_, hD⟩) ∧
      (∀ (σ : F ≃ₐ[K] F) (σ' : F' ≃ₐ[K'] F'), (∀ f : F, φ (σ f) = σ' (φ f)) →
        ∀ x : Pic0 K F, Ψ (σ • x) = σ' • Ψ x) := by sorry
