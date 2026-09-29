-- Prove2me | Theorems.Thm_FLT_OccurrenceStatement_three_dvd_coeff_heckeT_two_sub_smul_of_not_dvd
-- name    : FLT.OccurrenceStatement.three_dvd_coeff_heckeT_two_sub_smul_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/33786a34-d9d3-5ec4-9246-a9afe957a437
-- title:
--   Mod-3 Hecke congruence for the weight-one bridge product
-- statement:
--   Let $R$ be a commutative ring, $N$ a natural number, and $a : \mathbb{N} \to R$ a sequence of coefficients. Assume $a$ is an eigensystem for the weights $e(\ell) = 0$ when $\ell \mid N$ and $e(\ell) = \chi_{-3}(\ell)$ otherwise, where $\chi_{-3}(m)$ is $1$, $-1$ or $0$ according as $m \equiv 1$, $2$ or $0 \pmod 3$; that is, $a_1 = 1$ and, for every prime $\ell$ and every $n$, $a_{\ell n} + e(\ell)\cdot(a_{n/\ell}$ if $\ell \mid n$, else $0) = a_\ell a_n$. Let $\ell$ be a prime with $\ell \nmid N$, and let $n$ be a natural number. Put $F = (\sum_m a_m q^m)\cdot E$, where $E$ is the coefficientwise image in $R$ of the integral power series `e1Chi3` (constant term $1$, the $j$-th coefficient for $j>0$ being $6\,\sigma_\chi(j)$). Then $3$ divides, in $R$, the $n$-th coefficient of $\mathrm{heckeT}_{\ell,2}F - a_\ell\, F$, where $\mathrm{heckeT}_{\ell,2}$ is the $R$-linear operator whose $n$-th coefficient is $[q^{\ell n}]F + \ell\cdot([q^{n/\ell}]F$ if $\ell \mid n$, else $0)$.
--
--   This is the congruence underlying the passage from a weight-one eigensystem to a weight-two object in the style of Deligne–Serre: multiplying by the weight-one Eisenstein series attached to $\chi_{-3}$, which is $\equiv 1$ modulo $3$, turns the eigensystem into a power series that is a mod-$3$ eigenvector of the formal weight-two Hecke operators $T_\ell$ with eigenvalue $a_\ell$ at every prime $\ell \nmid N$. It is used by [`FLT.AbstractIntegralStructure.exists_weight_two_eigenform_congruent_of_isLatticeRealized`](thm.html#FLT.AbstractIntegralStructure.exists_weight_two_eigenform_congruent_of_isLatticeRealized) to produce a weight-two eigenform congruent to the given system modulo $3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FLT_OccurrenceStatement_three_dvd_coeff_heckeT_two_sub_smul_of_not_dvd.lean

import Mathlib
import Definitions.Def_FormalHecke_Eigensystem
import Definitions.Def_ModularForm_EisensteinChiNegThree
import Definitions.Def_CuspForm_IntegralLattice
import Definitions.Def_PowerSeries_FormalHeckeOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open EisensteinWeightOne

theorem FLT.OccurrenceStatement.three_dvd_coeff_heckeT_two_sub_smul_of_not_dvd
    {R : Type*} [CommRing R] {N : ℕ} {a : ℕ → R}
    (heig : FormalHecke.IsEigensystem
      (fun ℓ => if ℓ ∣ N then 0 else ((chiNegThree ℓ : ℤ) : R)) a)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (n : ℕ) :
    (3 : R) ∣ PowerSeries.coeff n
      (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a) := by sorry
