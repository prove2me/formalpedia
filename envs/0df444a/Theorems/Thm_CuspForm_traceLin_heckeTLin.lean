-- Prove2me | Theorems.Thm_CuspForm_traceLin_heckeTLin
-- name    : CuspForm.traceLin_heckeTLin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/c32f0144-27e0-56c6-be61-4529d615491c
-- title:
--   Level-lowering trace commutes with T_ℓ for ℓ ∤ M
-- statement:
--   Let $M$ and $q$ be natural numbers with $M \neq 0$, and let $A$ be an Atkin–Lehner datum for $(M,q)$, that is: a natural number $A.R$, a proof that $M = q \cdot A.R$, and integers $a, b$ with $q a - A.R\, b = 1$. Assume $q$ is prime. Let $\ell$ be a prime with $\ell \nmid M$ and $\ell \nmid A.R$, and let $f$ be a cusp form of weight $2$ on $\Gamma_0(M)$. The assertion is that the level-lowering trace $\mathrm{traceLin}$ attached to $A$, the $\mathbb{C}$-linear map $S_2(\Gamma_0(M)) \to S_2(\Gamma_0(A.R))$ sending $g$ to the form with underlying function $g + \mathrm{heckeU}\,2\,q\,(g \mid_2 A.\mathrm{alGL})$, where $\mathrm{heckeU}\,2\,q\,h = \sum_{j<q} h \mid_2 \mathrm{heckeMatrix}\,q\,j$, commutes with the Hecke operators at $\ell$: applying $\mathrm{heckeTLin}\,2$ at level $M$ (legitimate since $\ell \nmid M$) and then the trace gives the same weight-$2$ cusp form on $\Gamma_0(A.R)$ as applying the trace and then $\mathrm{heckeTLin}\,2$ at level $A.R$ (legitimate since $\ell \nmid A.R$). Here $\mathrm{heckeTLin}\,2$ is induced on cusp forms by $h \mapsto \mathrm{heckeU}\,2\,\ell\,h + h \mid_2 \mathrm{heckeDiagMatrix}\,\ell$.
--
--   This is the standard compatibility of the trace map $\mathrm{Tr}^M_R \colon S_2(\Gamma_0(M)) \to S_2(\Gamma_0(R))$, $M = qR$, with the Hecke operators $T_\ell$ at primes $\ell$ away from the level. It makes the $q$-new subspace cut out by such traces stable under $T_\ell$, and is used in [`CuspForm.apply_eq_zero_of_traceLin_eq_zero_of_forall_mem_newLattice`](thm.html#CuspForm.apply_eq_zero_of_traceLin_eq_zero_of_forall_mem_newLattice) and in the production of normalised new eigenforms from Hecke-algebra support.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_traceLin_heckeTLin.lean

import Mathlib
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.traceLin_heckeTLin {M q : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓR : ¬ ℓ ∣ A.R) (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    CuspForm.traceLin A hq (CuspForm.heckeTLin 2 hℓ hℓM f) = CuspForm.heckeTLin 2 hℓ hℓR (CuspForm.traceLin A hq f) := by sorry
