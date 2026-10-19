-- Prove2me | Theorems.Thm_CauchyRiemannIndex_isSymplectic_left_of_diamond
-- name    : CauchyRiemannIndex.isSymplectic_left_of_diamond
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T17:31:47.554996+00:00
-- url     : https://prove2.me/theorems/7faf5aec-53b2-4f51-bad3-962eef8c3b96
-- title:
--   If $A\diamond B$ is symplectic, then $A$ is symplectic
-- statement:
--   Let $A$ be a real $2n'\times2n'$ matrix and $B$ a real $2n''\times2n''$ matrix, and let $A\diamond B$ be their block-diagonal sum on $\mathbb R^{2(n'+n'')}$, acting by $A$ on the coordinates $(q',p')$ and by $B$ on $(q'',p'')$, with the coordinates ordered as $(q',q'',p',p'')$. If
--   $$A\diamond B\in\mathrm{Sp}(2(n'+n''),\mathbb R),$$
--   then $A\in\mathrm{Sp}(2n',\mathbb R)$. No assumption is made on $B$.
--
--   Together with the fact that the block sum of two symplectic matrices is symplectic, this identifies which matrices of $\mathrm{Sp}(2n)$ correspond to block sums inside $\mathrm{Sp}(2n+2n'')$. It is used when comparing $\mathrm{Sp}(2n)$ with $\mathrm{Sp}(2n+2)$.
--
--   **Formalization Note.** $\mathbb R^{2n\times2n}$ is `Mat n` (real matrices indexed by `Fin n ⊕ Fin n`, first block $q$, second block $p$) and $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ is `Matrix.J`; `IsSymplectic A` is membership in `Matrix.symplecticGroup`, i.e. $AJ_0A^T=J_0$. $A\diamond B$ is `ConleyZehnder.diamond A B` from the Conley-Zehnder setting definitions, the reindexing of `Matrix.fromBlocks A 0 0 B` along `(Fin n' ⊕ Fin n') ⊕ (Fin n'' ⊕ Fin n'') ≃ Fin (n'+n'') ⊕ Fin (n'+n'')`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, p. 62 (Theorem 3.34 and the Maslov index of loops in $\mathrm{Sp}(2n)$); J. Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse 23 (2014), arXiv:1307.7239, §2

import Definitions.Def_CauchyRiemannIndex_Setting
import Definitions.Def_ConleyZehnder_Setting

namespace CauchyRiemannIndex

open Matrix

/-- If the block-diagonal sum `A ⋄ B` is symplectic, then so is its first block `A`. -/
theorem isSymplectic_left_of_diamond {n' n'' : ℕ} (A : Mat n') (B : Mat n'')
    (h : IsSymplectic (ConleyZehnder.diamond A B)) : IsSymplectic A := by sorry

end CauchyRiemannIndex
