-- Prove2me | Theorems.Thm_AutomorphicForm_IsArchTestFactor_exists_isArchTestFactor_nonneg_norm_le
-- name    : AutomorphicForm.IsArchTestFactor.exists_isArchTestFactor_nonneg_norm_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/fbc2da6d-f18c-5b6f-affb-58ac606dc5fb
-- title:
--   Domination of an archimedean test factor by a nonnegative one
-- statement:
--   Let $F$ be a number field and let $\varphi_a \colon \mathrm{GL}_2(\mathbb{A}_{F,\infty}) \to \mathbb{C}$ be a function on the invertible $2\times 2$ matrices over the infinite adele ring of $F$ which is an archimedean test factor in the sense of the project predicate [`AutomorphicForm.IsArchTestFactor`](def/AutomorphicForm_FactorizableTestFn.html#L27): there is a function $\Phi$ on the space of $2\times 2$ arrays of elements of the mixed space $\prod_{v\ \mathrm{real}}\mathbb{R}\times\prod_{v\ \mathrm{complex}}\mathbb{C}$ of $F$ which is $C^\infty$ over $\mathbb{R}$ and satisfies $\varphi_a(g)=\Phi(\mathrm{archEntries}_F(g))$ for all $g$, where $\mathrm{archEntries}_F(g)$ is the array of entries of $g$ transported through the ring isomorphism between the infinite adele ring of $F$ and the mixed space; and $\varphi_a$ has compact support. The conclusion asserts the existence of a further function $\Psi$ on the same group which is again an archimedean test factor in this sense, which takes nonnegative real values in the sense that $\operatorname{Re}\Psi(g)\ge 0$ and $\operatorname{Im}\Psi(g)=0$ for every $g$, and which dominates $\varphi_a$ pointwise: $\lVert\varphi_a(g)\rVert \le \operatorname{Re}\Psi(g)$ for all $g \in \mathrm{GL}_2(\mathbb{A}_{F,\infty})$.
--
--   This is the elementary majorisation step needed because $|\varphi_a|$ is itself not smooth and constants are not compactly supported: a smooth compactly supported archimedean test factor is bounded in absolute value by a real nonnegative one of the same type. It is used in the estimate [`AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure`](thm.html#AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure), where an unsigned (lower-integral) orbital term must be bounded by the integral of a nonnegative test function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_IsArchTestFactor_exists_isArchTestFactor_nonneg_norm_le.lean

import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem AutomorphicForm.IsArchTestFactor.exists_isArchTestFactor_nonneg_norm_le
    (F : Type) [Field F] [NumberField F]
    (φa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hφa : AutomorphicForm.IsArchTestFactor F φa) :
    ∃ Ψ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
      AutomorphicForm.IsArchTestFactor F Ψ ∧
      (∀ g : GL (Fin 2) (InfiniteAdeleRing F), 0 ≤ (Ψ g).re ∧ (Ψ g).im = 0) ∧
      ∀ g : GL (Fin 2) (InfiniteAdeleRing F), ‖φa g‖ ≤ (Ψ g).re := by sorry
