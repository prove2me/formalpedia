-- Prove2me | Theorems.Thm_AutomorphicForm_ext_of_invariant_of_forall_glFin_eq_one_rat
-- name    : AutomorphicForm.ext_of_invariant_of_forall_glFin_eq_one_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/26893f93-57f2-57c8-9f02-cc9577ac3c30
-- title:
--   Left GL₂(ℚ)- and right K₁(N)-invariant functions agree
-- statement:
--   Let $M$ be any type, let $N$ be a nonzero ideal of the ring of integers of $\mathbb{Q}$, and let $\Psi_1,\Psi_2$ be two functions from $\mathrm{GL}_2$ of the adele ring of $\mathbb{Q}$ to $M$. Assume: (i) each $\Psi_i$ is invariant under left multiplication by every element of the image of [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15), i.e. by $\gamma \in \mathrm{GL}_2(\mathbb{Q})$ pushed into $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ entrywise along the structure map $\mathbb{Q}\to\mathbb{A}_\mathbb{Q}$; (ii) each $\Psi_i$ is invariant under right multiplication by [`AdelicDock.finEmbed`](def/AdelicDock_LocalEmbedding.html#L145) $u$ for every $u$ in the subgroup [`NumberField.AdelicLevel.finiteLevelOne`](def/NumberField_AdelicLevel.html#L418) at $N$, that is, every finite-adelic $u$ such that both $u$ and $u^{-1}$ satisfy the predicate `IsLevelOneMatrix` for $N$ (the level-zero condition `IsLevelZeroMatrix` together with the lower-right entry lying in $1 +$ the ideal ball of $N$), embedded into $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ with identity archimedean component; (iii) $\Psi_1 h = \Psi_2 h$ holds for every adelic $h$ whose finite component `glFin` $h$ is the identity and whose real component [`LanglandsTunnell.ratArchGL2`](def/LanglandsTunnell_DeltaLift.html#L16) $h$, obtained from the archimedean component at the real place of $\mathbb{Q}$, lies in $\mathrm{GL}_2^{+}(\mathbb{R})$. Then $\Psi_1 = \Psi_2$ as functions.
--
--   This is the uniqueness half of the classical–adelic dictionary for modular forms: a function on $\mathrm{GL}_2(\mathbb{Q})\backslash \mathrm{GL}_2(\mathbb{A}_\mathbb{Q})/K_1(N)$ is determined by its values on elements trivial at the finite places and of positive determinant at infinity, hence by its restriction to $\mathrm{GL}_2^{+}(\mathbb{R})$. It is used in the comparison of adelic lifts of classical cusp forms with their Hecke eigensystems, in particular in the newform and nebentypus computations that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_ext_of_invariant_of_forall_glFin_eq_one_rat.lean

import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.ext_of_invariant_of_forall_glFin_eq_one_rat
    {M : Type*} {N : Ideal (NumberField.RingOfIntegers ℚ)} (hN : N ≠ ⊥)
    {Ψ₁ Ψ₂ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → M}
    (h₁ : ∀ (γ : GL (Fin 2) ℚ) (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
      Ψ₁ (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * x) = Ψ₁ x)
    (h₂ : ∀ (γ : GL (Fin 2) ℚ) (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
      Ψ₂ (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * x) = Ψ₂ x)
    (h₁' : ∀ u ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ N,
      ∀ x, Ψ₁ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) = Ψ₁ x)
    (h₂' : ∀ u ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ N,
      ∀ x, Ψ₂ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) = Ψ₂ x)
    (heq : ∀ h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
      NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
        LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ → Ψ₁ h = Ψ₂ h) :
    Ψ₁ = Ψ₂ := by sorry
