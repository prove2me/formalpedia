-- Prove2me | Theorems.Thm_CuspForm_exists_isLatticeRealized_of_isWeightOneChiNegThreeRealized_of_three_dvd
-- name    : CuspForm.exists_isLatticeRealized_of_isWeightOneChiNegThreeRealized_of_three_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/12b6c370-978d-5245-8029-85b82f134c07
-- title:
--   Weight-one eigensystem realised mod 3 in weight two
-- statement:
--   Let $M$ be a nonzero natural number divisible by $3$, and let $b\colon\mathbb N\to\mathbb Z[\sqrt{-2}]$ be a sequence in $\mathbb Z[\sqrt{-2}]$. Write $e_\ell = 0$ if $\ell\mid M$ and $e_\ell=\chi_{-3}(\ell)$ otherwise, where $\chi_{-3}(n)$ is $1$, $-1$ or $0$ according as $n\equiv 1$, $2$ or $0 \bmod 3$, viewed in the relevant coefficient ring. Assume: (i) $b$ is a formal Hecke eigensystem for these $e_\ell$ over $\mathbb Z[\sqrt{-2}]$, that is $b_1=1$ and $b_{\ell n}+e_\ell\cdot(b_{n/\ell}$ if $\ell\mid n$, else $0)=b_\ell b_n$ for every prime $\ell$ and every $n$; (ii) the space of weight-two cusp forms on $\Gamma_0(M)$ is spanned over $\mathbb C$ by those forms all of whose $q$-expansion coefficients lie in the bottom subring of $\mathbb C$ (the image of $\mathbb Z$); (iii) there exist a ring homomorphism $\iota\colon\mathbb Z[\sqrt{-2}]\to\mathbb C$ and a cusp form $f$ of weight one on $\Gamma_1(M)$ with $n$-th $q$-expansion coefficient $\iota(b_n)$ for every $n$ (no nebentypus condition is imposed in this hypothesis beyond what (i) encodes). Then there is an integer-valued sequence $a\colon\mathbb N\to\mathbb Z$ such that: $a$ is a formal Hecke eigensystem over $\mathbb Z$ for the same $e_\ell$; $a$ is lattice-realised at level $M$, i.e. there are a weight-two cusp form $F$ on $\Gamma_0(M)$ with all $q$-coefficients in the bottom subring of $\mathbb C$ and integers $c_n$ with $(c_n:\mathbb C)$ equal to the $n$-th $q$-coefficient of $F$, such that $3\mid c_n-\big(\mathrm{mk}(a)\cdot \mathtt{e1Chi3In}\ \mathbb Z\big)_n$ for all $n$, the second factor being the weight-one Eisenstein power series attached to $\chi_{-3}$; and $a_n \bmod 3$ equals $\mathrm{red}(b_n)$ for every $n$, where $\mathrm{red}\colon\mathbb Z[\sqrt{-2}]\to\mathbb Z/3$ is the ring homomorphism sending $\sqrt{-2}$ to $-1$.
--
--   This is Wiles's Eisenstein trick carried out directly at a level divisible by $3$: multiplication by the weight-one Eisenstein series of nebentypus $\chi_{-3}$, which is congruent to $1$ modulo $3$, transports a weight-one eigensystem with coefficients in $\mathbb Z[\sqrt{-2}]$ to an integral eigensystem realised modulo $3$ inside the integral lattice of weight-two cusp forms on $\Gamma_0(M)$, with no divisibility of the level by $9$ required. It feeds the weight-one newform existence statements [`FLT.No2BridgeWiring.weightOneNewformExists_levelAtThree_not_cube_dvd`](thm.html#FLT.No2BridgeWiring.weightOneNewformExists_levelAtThree_not_cube_dvd) and [`FLT.No2BridgeWiring.weightOneNewformExists_not_cube_dvd`](thm.html#FLT.No2BridgeWiring.weightOneNewformExists_not_cube_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_isLatticeRealized_of_isWeightOneChiNegThreeRealized_of_three_dvd.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_WeightOneRealizationCarriers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FLT.ExplicitLift EisensteinWeightOne CuspForm

theorem CuspForm.exists_isLatticeRealized_of_isWeightOneChiNegThreeRealized_of_three_dvd
    (M : ℕ) [NeZero M] (h3 : 3 ∣ M) (b : ℕ → ℤ√(-2))
    (heig : FormalHecke.IsEigensystem
      (fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ√(-2))) b)
    (hbasis : CuspForm.HasIntegralBasis M)
    (hreal : CuspForm.IsWeightOneChiNegThreeRealized M b) :
    ∃ a : ℕ → ℤ,
      FormalHecke.IsEigensystem (fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ)) a ∧
      CuspForm.IsLatticeRealized M a ∧
      ∀ n : ℕ, ((a n : ℤ) : ZMod 3) = red (b n) := by sorry
