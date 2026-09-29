-- Prove2me | Theorems.Thm_CuspForm_heckeULin_apply_eq_smul_iff
-- name    : CuspForm.heckeULin_apply_eq_smul_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/aa730063-b4a8-5592-bbc1-a22d92ae5438
-- title:
--   Uₚ-eigenform criterion on q-expansion coefficients
-- statement:
--   Let $N$ be a natural number with $N \neq 0$, let $k \in \mathbb{Z}$, and let $p$ be a natural number dividing $N$. Let $f$ be a cusp form of weight $k$ for $\Gamma_0(N)$ and let $c \in \mathbb{C}$. The assertion is an equivalence between two statements. The first is the equality $\mathtt{heckeULin}\,k\,hpN\,(f) = c \cdot f$ in the space of cusp forms of weight $k$ for $\Gamma_0(N)$, where [`CuspForm.heckeULin k hpN`](def/ModularForm_HeckeOperatorForms.html#L83) is the $\mathbb{C}$-linear endomorphism of that space whose underlying function sends $f$ to $\sum_{j=0}^{p-1} f \mid[k] \,\mathtt{heckeMatrix}\,p\,j$, the weight-$k$ slash action summed over the $p$ matrices used for $U_p$. The second is that for every natural number $n$ one has $a_{np} = c\,a_n$, where $a_n = \mathtt{qCoeff}\,f\,n$ denotes the $n$-th coefficient of the $q$-expansion of $f$ at the cusp $\infty$ with period $1$, and $\mathtt{coeffHeckeU}\,p$ is the coefficientwise operator $a \mapsto (n \mapsto a_{np})$. Thus $f$ is an eigenvector of $U_p$ with eigenvalue $c$ exactly when its $q$-expansion coefficients satisfy $a_{np} = c\,a_n$ for all $n \geq 0$ (including $n = 0$).
--
--   This is the standard criterion identifying $U_p$-eigenforms, for $p \mid N$, in terms of the relation $a_{np} = c\,a_n$ on $q$-expansion coefficients, here for the bundled linear operator on $S_k(\Gamma_0(N))$ rather than for the operator on functions on the upper half-plane. It is used in the construction of normalised eigenforms, for instance in [`CuspForm.HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq`](thm.html#CuspForm.HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq) and in the statements producing eigenforms whose annihilator lies in a given prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_heckeULin_apply_eq_smul_iff.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.heckeULin_apply_eq_smul_iff {N : ℕ} [NeZero N] (k : ℤ) {p : ℕ} (hpN : p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (c : ℂ) :
    CuspForm.heckeULin k hpN f = c • f ↔
      ∀ n : ℕ, ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n = c * ModularFormClass.qCoeff f n := by sorry
