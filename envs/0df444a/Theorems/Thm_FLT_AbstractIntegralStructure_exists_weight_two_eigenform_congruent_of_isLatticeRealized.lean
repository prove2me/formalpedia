-- Prove2me | Theorems.Thm_FLT_AbstractIntegralStructure_exists_weight_two_eigenform_congruent_of_isLatticeRealized
-- name    : FLT.AbstractIntegralStructure.exists_weight_two_eigenform_congruent_of_isLatticeRealized
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/f83d53c9-fad9-502c-83f0-323dbb8e5601
-- title:
--   Weight-one χ₋₃ eigensystem occurs mod 3 in weight two
-- statement:
--   Fix a positive level $N$ (given as a natural number with `NeZero N`). Assume [`CuspForm.HasIntegralBasis N`](def/CuspForm_IntegralLattice.html#L17), the project's integrality hypothesis at level $N$: the $\mathbb{C}$-span of the set [`CuspForm.qIntegralSet N`](def/CuspForm_IntegralLattice.html#L11) of weight-two cusp forms on $\Gamma_0(N)$ all of whose $q$-expansion coefficients `qCoeff` lie in the bottom subring of $\mathbb{C}$ (i.e. are rational integers) is the whole space. Let $a : \mathbb{N} \to \mathbb{Z}$ be a sequence satisfying [`FormalHecke.IsEigensystem`](def/FormalHecke_Eigensystem.html#L10) for the system of eigenvalue-data $\ell \mapsto 0$ if $\ell \mid N$ and $\ell \mapsto \chi_{-3}(\ell)$ otherwise, where $\chi_{-3}(n)$ is $1$, $-1$ or $0$ according as $n \equiv 1, 2, 0 \pmod 3$; unfolded, this says $a_1 = 1$ and, for every prime $\ell$ and every $n$, $a_{\ell n} + e_\ell\cdot a_{n/\ell}\,[\ell \mid n] = a_\ell a_n$ with $e_\ell$ as above — the weight-one shape of the recursion. Assume further [`CuspForm.IsLatticeRealized N a`](def/CuspForm_IntegralLattice.html#L27): there is a weight-two cusp form on $\Gamma_0(N)$ with all `qCoeff` in $\mathbb{Z}$, given by an integer sequence $a^f$, such that $3 \mid a^f_n - \mathrm{coeff}_n(\mathrm{bridgeProduct}\,a)$ for all $n$, where $\mathrm{bridgeProduct}\,a$ is the formal product of $\sum a_n q^n$ with the power series `e1Chi3` having constant term $1$ and $n$-th coefficient $6\sigma_{\chi_{-3}}(n)$. The conclusion asserts the existence of $f \in S_2(\Gamma_0(N))$ satisfying the project's predicate [`CuspForm.IsNormalizedEigenform`](def/FLTPrelim_Modularity.html#L28) (namely $\mathrm{qCoeff}\,f\,1 = 1$, multiplicativity of the coefficients on coprime indices, and the weight-two three-term recursions at prime powers, with the $p\,\mathrm{qCoeff}\,f\,p^r$ term present exactly when $p \nmid N$), together with a maximal ideal $\mathfrak{m}'$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ containing $3$, such that for every prime $\ell \nmid N$ there is an element $c$ of that integral closure with $c = \mathrm{qCoeff}\,f\,\ell$ in $\mathbb{C}$ and $c - a_\ell \in \mathfrak{m}'$. Thus the $\ell$-th coefficient of $f$ is an algebraic integer congruent to $a_\ell$ modulo $\mathfrak{m}'$, for all primes $\ell$ not dividing $N$; no assertion is made at primes dividing $N$.
--
--   This is the occurrence step of the weight-one-to-weight-two congruence used in the Langlands–Tunnell input to modularity, in the spirit of Deligne–Serre's lifting lemma (Lemme 6.11 of their paper on weight-one forms) as deployed in Darmon–Diamond–Taylor, §4.1. It differs from the textbook statement in being entirely conditional on two project hypotheses — [`CuspForm.HasIntegralBasis N`](def/CuspForm_IntegralLattice.html#L17) in span form and [`CuspForm.IsLatticeRealized N a`](def/CuspForm_IntegralLattice.html#L27), the latter encoding the mod-$3$ realisation of the bridge product $(\sum a_n q^n)\cdot E_1(1,\chi_{-3})$ by an integral weight-two cusp form — and in using the project's coefficient-level axiomatisation of a normalised eigenform and of a Hecke eigensystem in place of Hecke-operator statements. It is used in the proof that a semistable integral Weierstrass model with nonzero discriminant and irreducible mod-$3$ representation is residually modular at $3$ of some level $M$ with controlled ramification.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FLT_AbstractIntegralStructure_exists_weight_two_eigenform_congruent_of_isLatticeRealized.lean

import Mathlib
import Definitions.Def_CuspForm_IntegralLattice
import Definitions.Def_FormalHecke_Eigensystem
import Definitions.Def_ModularForm_EisensteinChiNegThree
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CuspForm EisensteinWeightOne CongruenceSubgroup ModularFormClass

theorem FLT.AbstractIntegralStructure.exists_weight_two_eigenform_congruent_of_isLatticeRealized
    {N : ℕ} [NeZero N] (h : CuspForm.HasIntegralBasis N) {a : ℕ → ℤ}
    (heig : FormalHecke.IsEigensystem
      (fun ℓ => if ℓ ∣ N then 0 else ((chiNegThree ℓ : ℤ) : ℤ)) a)
    (hreal : CuspForm.IsLatticeRealized N a) :
    ∃ (f : CuspForm (Gamma0 N) 2) (_ : f.IsNormalizedEigenform)
      (𝔪' : Ideal (integralClosure ℤ ℂ)), 𝔪'.IsMaximal ∧
      ((3 : ℕ) : integralClosure ℤ ℂ) ∈ 𝔪' ∧
      ∀ (ℓ : ℕ) (_ : ℓ.Prime) (_ : ¬ ℓ ∣ N),
        ∃ c : integralClosure ℤ ℂ, (c : ℂ) = ModularFormClass.qCoeff f ℓ ∧
          c - (a ℓ : integralClosure ℤ ℂ) ∈ 𝔪' := by sorry
