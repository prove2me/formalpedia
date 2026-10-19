-- Prove2me | Theorems.Thm_CauchyRiemannIndex_diamond_isSymplectic
-- name    : CauchyRiemannIndex.diamond_isSymplectic
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T16:49:27.934901+00:00
-- url     : https://prove2.me/theorems/e1aaab64-ea26-4f43-af23-9c3ab099b221
-- title:
--   The block sum $A\diamond B$ of symplectic matrices is symplectic
-- statement:
--   If $A\in\mathrm{Sp}(2n',\mathbb R)$ and $B\in\mathrm{Sp}(2n'',\mathbb R)$, then
--   $$A\diamond B\in\mathrm{Sp}(2(n'+n''),\mathbb R),$$
--   where $A\diamond B$ is the block-diagonal matrix acting by $(q',q'',p',p'')\mapsto$ ($A$ on $(q',p')$, $B$ on $(q'',p'')$), i.e. the matrix of $A\oplus B$ on $\mathbb R^{2n'}\oplus\mathbb R^{2n''}=\mathbb R^{2(n'+n'')}$ with the coordinates reordered as $(q',q'',p',p'')$.
--
--   This is the product structure on symplectic groups used for the product property of the Conley-Zehnder index (Gutt, §2) and for comparing $\mathrm{Sp}(2n)$ with $\mathrm{Sp}(2n+2)$.
--
--   **Formalization Note.** $\mathbb R^{2n\times2n}$ is `Mat n` (real matrices indexed by `Fin n ⊕ Fin n`, first block $q$, second block $p$) and $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ is `Matrix.J`; `IsSymplectic A` is membership in `Matrix.symplecticGroup`. Vectors of $\mathbb R^{2n}$ are functions `Fin n ⊕ Fin n → ℝ` and $Av$ is `A *ᵥ v`. $A\diamond B$ is `ConleyZehnder.diamond A B` from the Conley-Zehnder setting definitions, the reindexing of `Matrix.fromBlocks A 0 0 B` along `(Fin n' ⊕ Fin n') ⊕ (Fin n'' ⊕ Fin n'') ≃ Fin (n'+n'') ⊕ Fin (n'+n'')`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, p. 62 (Theorem 3.34 and the Maslov index of loops in $\mathrm{Sp}(2n)$); J. Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse 23 (2014), arXiv:1307.7239, §2 (the map $\hat\rho$, eq. (9))

import Definitions.Def_CauchyRiemannIndex_Setting
import Definitions.Def_ConleyZehnder_Setting

namespace CauchyRiemannIndex

open Matrix

/-- The block-diagonal sum `A ⋄ B` of symplectic matrices is symplectic. -/
theorem diamond_isSymplectic {n' n'' : ℕ} (A : Mat n') (B : Mat n'') (hA : IsSymplectic A)
    (hB : IsSymplectic B) : IsSymplectic (ConleyZehnder.diamond A B) := by sorry

end CauchyRiemannIndex
