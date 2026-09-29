-- Prove2me | Theorems.Thm_CohCarrier_finrank_parabolicHoms_complex_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity
-- name    : CohCarrier.finrank_parabolicHoms_complex_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/1cd69e28-8c04-5620-9eb9-eb74686535f0
-- title:
--   Dimension of g-isotypic parabolic classes at level N
-- statement:
--   Let $N\ge 1$, let $S$ be a finite set of natural numbers all of whose elements are prime and which contains every prime divisor of $N$, let $M_g\ge 1$ divide $N$, let $g$ be a weight-two cusp form on $\Gamma_0(M_g)$ which is a newform in the project's sense (a normalised eigenform, i.e. $a_1(g)=1$ with the multiplicativity and Hecke recursions for its $q$-expansion coefficients [`ModularFormClass.qCoeff`](def/FLTPrelim_Modularity.html#L19), and such that no proper divisor of $M_g$ carries a normalised eigenform with the same coefficients at primes not dividing $M_g$), and let $\mu:\mathbb N\to\mathbb C$ be arbitrary. Work in [`CohCarrier.H1 N ⊤ ℂ`](def/CohCarrier_Level.html#L162), the additive homomorphisms from `Additive (CohCarrier.GammaH N ⊤)` — the group $\Gamma_0(N)\subseteq \mathrm{SL}_2(\mathbb Z)$ — to $\mathbb C$, with the transfer Hecke operators $T_\ell=$ [`CohCarrier.heckeTL N ⊤ ℂ ℓ`](def/CohCarrier_Inst.html#L23) (pull back along conjugation by the upper-triangular matrix at $\ell$, then corestrict) and the parabolic submodule [`ModularCurve.Period.parabolicHoms`](def/ModularCurve_PeriodMap.html#L62) of homomorphisms vanishing on all $\gamma$ with $\mathrm{tr}(\gamma)^2=4$. Then: (A) for every prime $\ell\nmid N$ and every $\nu\in\mathbb C$, a parabolic class lying in the maximal generalised $\nu$-eigenspace of $T_\ell$ lies in the $\nu$-eigenspace; and (B) the $\mathbb C$-dimension of the intersection of the parabolic submodule with the $a_\ell(g)$-eigenspaces of $T_\ell$ over all primes $\ell\notin S$ and with the maximal generalised $\mu_q$-eigenspaces of $T_q$ over all primes $q\mid N$ equals $2\prod_{q\mid N}\operatorname{mult}_{\mu_q}(P_q)$, the product over the prime factors of $N$, where, with $e=v_q(N)-v_q(M_g)$, $P_q=X-a_q(g)$ if $e=0$ and $P_q=X^{e-1}\bigl(X^2-a_q(g)X+c_q\bigr)$ otherwise, with $c_q=0$ if $q\mid M_g$ and $c_q=q$ otherwise.
--
--   This is the Eichler–Shimura form of the Atkin–Lehner–Li old-space dimension count: it computes, over the complex numbers, the size of the part of the parabolic cohomology of $\Gamma_0(N)$ cut out by the eigensystem of a newform $g$ of level $M_g\mid N$ together with prescribed generalised eigenvalues for the operators at the primes dividing $N$, the factor $2$ coming from the two copies of the space of cusp forms in the Eichler–Shimura isomorphism. It is the complex-coefficient input for the corresponding dimension statement [`CohCarrier.finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity`](thm.html#CohCarrier.finrank_parabolicHoms_inf_iInf_eigenspace_heckeTL_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_finrank_parabolicHoms_complex_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity.lean

import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CuspForm_Newforms
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Polynomial.Roots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem CohCarrier.finrank_parabolicHoms_complex_inf_iInf_eigenspace_inf_iInf_maxGenEigenspace_eq_two_mul_prod_rootMultiplicity
    (N : ℕ) [NeZero N] (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (Mg : ℕ) [NeZero Mg] (hMgN : Mg ∣ N)
    (g : CuspForm (CongruenceSubgroup.Gamma0 Mg) 2) (hg : g.IsNewform) (mu : ℕ → ℂ) :

    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ∀ ν : ℂ,
      ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH N ⊤) ℂ ⊓
          Module.End.maxGenEigenspace (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL N ⊤ ℂ ℓ) ν ≤
        Module.End.eigenspace (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL N ⊤ ℂ ℓ) ν) ∧

    Module.finrank ℂ
      ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH N ⊤) ℂ ⊓
        (⨅ (ℓ : ℕ) (hℓ : ℓ.Prime) (_ : ℓ ∉ S), Module.End.eigenspace
          (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL N ⊤ ℂ ℓ) (ModularFormClass.qCoeff g ℓ)) ⊓
        (⨅ (q : ℕ) (hq : q.Prime) (_ : q ∣ N), Module.End.maxGenEigenspace
          (haveI : NeZero q := ⟨hq.ne_zero⟩; CohCarrier.heckeTL N ⊤ ℂ q) (mu q))) =
    2 * ∏ q ∈ N.primeFactors, Polynomial.rootMultiplicity (mu q)
      (let e : ℕ := N.factorization q - Mg.factorization q
       if e = 0 then X - C (ModularFormClass.qCoeff g q)
       else X ^ (e - 1) * (X ^ 2 - C (ModularFormClass.qCoeff g q) * X +
         C (if q ∣ Mg then (0 : ℂ) else (q : ℂ)))) := by sorry
