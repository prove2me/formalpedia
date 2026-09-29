-- Prove2me | Theorems.Thm_CuspForm_qCoeffLinear_apply
-- name    : CuspForm.qCoeffLinear_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/23cfa0e5-d557-5a31-8291-af0dc831f3b5
-- title:
--   Evaluation of the n-th q-coefficient functional
-- statement:
--   Let $M$ be a natural number (the level), $k$ an integer (the weight), $n$ a natural number, and let $f$ be a cusp form of weight $k$ for the congruence subgroup $\Gamma_0(M)$, i.e. an element of `CuspForm (CongruenceSubgroup.Gamma0 M) k`. The assertion is that the value at $f$ of the $\mathbb{C}$-linear functional [`CuspForm.qCoeffLinear M k n`](def/CuspForm_QCoeffLinear.html#L15) equals [`ModularFormClass.qCoeff (⇑f) n`](def/FLTPrelim_Modularity.html#L19), the $n$-th coefficient of the $q$-expansion of the underlying function $\mathbb{H} \to \mathbb{C}$ of $f$, where [`ModularFormClass.qCoeff g n`](def/FLTPrelim_Modularity.html#L19) is by definition the coefficient of $q^n$ in `qExpansion 1 g`, the $q$-expansion taken with width $1$. Thus the linear map [`CuspForm.qCoeffLinear`](def/CuspForm_QCoeffLinear.html#L15), whose underlying function is precisely $f \mapsto$ [`ModularFormClass.qCoeff (⇑f) n`](def/FLTPrelim_Modularity.html#L19) and whose additivity and $\mathbb{C}$-homogeneity are supplied in its definition, is identified with the naive coefficient map on the level of values.
--
--   This is the evaluation rule for the functional $f \mapsto a_n(f)$ on $S_k(\Gamma_0(M))$: it lets the additivity and homogeneity packaged in [`CuspForm.qCoeffLinear`](def/CuspForm_QCoeffLinear.html#L15) be transported to statements phrased directly in terms of [`ModularFormClass.qCoeff`](def/FLTPrelim_Modularity.html#L19). It is used in the construction of integral structures on spaces of cusp forms ([`CuspForm.hasIntegralStructure_two`](thm.html#CuspForm.hasIntegralStructure_two)) and in the vanishing statements [`ModPForms.modPCusp_eq_bot_of_neg`](thm.html#ModPForms.modPCusp_eq_bot_of_neg) and [`ModPForms.modPMod_eq_bot_of_neg`](thm.html#ModPForms.modPMod_eq_bot_of_neg).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_qCoeffLinear_apply.lean

import Mathlib
import Definitions.Def_CuspForm_QCoeffLinear

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.qCoeffLinear_apply (M : ℕ) (k : ℤ) (n : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) :
    CuspForm.qCoeffLinear M k n f = ModularFormClass.qCoeff (⇑f) n := by sorry
