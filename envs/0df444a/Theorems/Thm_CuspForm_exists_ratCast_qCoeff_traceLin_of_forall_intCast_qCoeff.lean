-- Prove2me | Theorems.Thm_CuspForm_exists_ratCast_qCoeff_traceLin_of_forall_intCast_qCoeff
-- name    : CuspForm.exists_ratCast_qCoeff_traceLin_of_forall_intCast_qCoeff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/dbd92dc0-dbb3-58cc-8b17-efbd0fecd8e4
-- title:
--   Rationality of q-coefficients of level-lowering traces
-- statement:
--   Let $M,q$ be natural numbers with $M$ nonzero, and let $A$ be an Atkin–Lehner datum of level $M$ at $q$, that is, a natural number $A.R$ together with a factorisation $M = q\,A.R$ and integers $a,b$ satisfying $qa - A.R\,b = 1$; assume $q$ is prime. Let $f$ be a cusp form of weight $2$ for $\Gamma_0(M)$ all of whose $q$-expansion coefficients at $\infty$ are rational integers, i.e. for every $n$ there is $m \in \mathbb{Z}$ with $\mathrm{qCoeff}\,f\,n = m$ in $\mathbb{C}$. Then for every natural number $n$ two rationality assertions hold simultaneously: the $n$-th coefficient of the $q$-expansion (taken with period $1$) of the weight-$2$ cusp form [`CuspForm.traceLin A hq f`](def/CuspForm_LevelLoweringTrace.html#L18) on $\Gamma_0(A.R)$, whose underlying function is $f + \sum_{j<q} \bigl(f\mid_2 A.\mathrm{alGL}\bigr)\mid_2 \mathrm{heckeMatrix}\,q\,j$, lies in the image of $\mathbb{Q}$ in $\mathbb{C}$; and likewise the $n$-th such coefficient of [`CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 f)`](def/CuspForm_LevelLoweringTrace.html#L18), obtained by applying the same construction to the cusp form with underlying function $f\mid_2 A.\mathrm{alGL}$, lies in the image of $\mathbb{Q}$.
--
--   This is the rationality statement for the level-lowering trace $S_2(\Gamma_0(M)) \to S_2(\Gamma_0(M/q))$ and for its composition with the Atkin–Lehner operator at $q$: integrality of the $q$-expansion of $f$ need not be preserved (denominators appear), but no irrationality is introduced. It is used in the analysis of the $q$-new part of $S_2(\Gamma_0(M))$, in particular by [`CuspForm.apply_eq_zero_of_traceLin_eq_zero_of_forall_mem_newLattice`](thm.html#CuspForm.apply_eq_zero_of_traceLin_eq_zero_of_forall_mem_newLattice) and by the two statements on integral multiples of the coefficients of $f\mid_2 A.\mathrm{alGL}$ for forms in the integral lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_ratCast_qCoeff_traceLin_of_forall_intCast_qCoeff.lean

import Definitions.Def_CuspForm_NewLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.exists_ratCast_qCoeff_traceLin_of_forall_intCast_qCoeff
    {M q : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    (hf : ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff f n = (m : ℂ)) (n : ℕ) :
    (∃ r : ℚ, ModularFormClass.qCoeff (⇑(CuspForm.traceLin A hq f)) n = (r : ℂ)) ∧
    (∃ r : ℚ, ModularFormClass.qCoeff
      (⇑(CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 f))) n = (r : ℂ)) := by sorry
