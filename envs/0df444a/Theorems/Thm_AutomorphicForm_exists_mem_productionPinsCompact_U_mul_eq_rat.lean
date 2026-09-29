-- Prove2me | Theorems.Thm_AutomorphicForm_exists_mem_productionPinsCompact_U_mul_eq_rat
-- name    : AutomorphicForm.exists_mem_productionPinsCompact_U_mul_eq_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/e2084150-2207-5eb9-a4b9-4f2e4aad028a
-- title:
--   Adelic decomposition GL₂(A_ℚ)=GL₂(ℚ)· h· U₁(N)
-- statement:
--   Let $N$ be a nonzero ideal of the ring of integers of $\mathbb{Q}$ and let $g$ be an element of $\mathrm{GL}_2$ over the adele ring of $\mathbb{Q}$. The assertion is that there exist $\gamma \in \mathrm{GL}_2(\mathbb{Q})$ and two adelic matrices $h, u \in \mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ with the following four properties. First, $u$ lies in the level subgroup attached to $N$ by `productionPinsCompact ℚ`, which by construction is the intersection of [`NumberField.AdelicLevel.levelOne`](def/NumberField_AdelicLevel.html#L589) at $N$ — the preimage under the finite-part map `glFin` of the subgroup `finiteLevelOne` at $N$ — with `finiteAdelicGL2Subgroup`, the kernel of the archimedean-part map `glArch`; thus $u$ has trivial archimedean part and finite part of level $N$. Secondly, `glFin` applied to $h$ is the identity, so $h$ is purely archimedean. Thirdly, for every real infinite place $w$ of $\mathbb{Q}$, the $w$-component of the archimedean part of $h$, transported to $\mathrm{GL}_2(\mathbb{R})$ along the isomorphism `ringEquivRealOfIsReal` of $w$'s completion with $\mathbb{R}$, has positive determinant. Finally, $g$ equals the product of the diagonal image `globalPoints` of $\gamma$, then $h$, then $u$.
--
--   This is the strong-approximation decomposition $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q}) = \mathrm{GL}_2(\mathbb{Q})\cdot \mathrm{GL}_2(\mathbb{R})^{+}\cdot K_1(N)$, stated for the level subgroups of the compact production data `productionPinsCompact ℚ`. It is the covering statement used when a classical modular form of level $\Gamma_1(N)$ is lifted to a function on the adelic group, by evaluating the archimedean factor $h$; it is cited in the construction of the adelic lift of weight-one dihedral forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_mem_productionPinsCompact_U_mul_eq_rat.lean

import Definitions.Def_AutomorphicForm_ProductionPinsCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AutomorphicForm.exists_mem_productionPinsCompact_U_mul_eq_rat
    {N : Ideal (NumberField.RingOfIntegers ℚ)} (hN : N ≠ ⊥)
    (g : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
    ∃ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ)
      (h u : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)),
      u ∈ (AutomorphicForm.productionPinsCompact ℚ).U N ∧
        NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 ∧
        (∀ (w : NumberField.InfinitePlace ℚ) (hw : w.IsReal),
          Matrix.GeneralLinearGroup.map
              (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom
              (NumberField.AdelicLevel.archComponent ℚ w
                (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ h))
            ∈ Matrix.GLPos (Fin 2) ℝ) ∧
        g = AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * h * u := by sorry
