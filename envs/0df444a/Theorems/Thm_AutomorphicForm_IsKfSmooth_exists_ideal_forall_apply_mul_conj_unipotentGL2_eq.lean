-- Prove2me | Theorems.Thm_AutomorphicForm_IsKfSmooth_exists_ideal_forall_apply_mul_conj_unipotentGL2_eq
-- name    : AutomorphicForm.IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/dc8d5401-7d44-5f6e-a7b9-523518430b63
-- title:
--   K_f-smooth functions admit a level of unipotent invariance
-- statement:
--   Let $F$ be a number field and let $\varphi$ be a complex-valued function on $\mathrm{GL}_2(\mathbb{A}_F)$, the group of invertible $2\times 2$ matrices over the adele ring of $F$. Assume $\varphi$ is $K_f$-smooth, meaning that, for the right-translation action on functions, the stabiliser of $\varphi$ inside `finiteAdelicGL2Subgroup`, the kernel of the archimedean-component homomorphism `glArch` (so the subgroup of adelic matrices with trivial archimedean part), is an open subgroup. The conclusion is that there exists a nonzero ideal $\mathfrak{n}$ of $\mathcal{O}_F$ with the following property: for all $g, x \in \mathrm{GL}_2(\mathbb{A}_F)$ such that the finite component `glFin x` lies in the subgroup `finiteIntegralGL2` (the elements $h$ of $\mathrm{GL}_2$ of the finite adeles for which both $h$ and $h^{-1}$ satisfy the predicate `IsLevelZeroMatrix` at the unit ideal, an integrality condition), and for every adele $t$ whose archimedean component `adeleArch t` vanishes and whose finite component `adeleFin t` lies in `idealBall 𝔫`, i.e. satisfies $v(t_v) \le \exp(-\mathrm{ord}_v(\mathfrak{n}))$ at every height-one prime $v$ of $\mathcal{O}_F$, one has $\varphi\bigl(g\,(x^{-1}\,n(t)\,x)\bigr) = \varphi(g)$, where $n(t)$ denotes the unipotent matrix $\begin{pmatrix}1 & t\\ 0 & 1\end{pmatrix}$.
--
--   This records the level structure of a $K_f$-smooth function on adelic $\mathrm{GL}_2$: openness of the stabiliser yields a single nonzero ideal $\mathfrak{n}$ such that $\varphi$ is right-invariant under all unipotents $n(t)$ with $t$ in the corresponding ball, conjugated by elements with integral finite component. It is used in the analysis of constant terms and Whittaker coefficients of smooth automorphic functions, for instance in the vanishing and summability statements for Whittaker coefficients of $K_f$-smooth functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_IsKfSmooth_exists_ideal_forall_apply_mul_conj_unipotentGL2_eq.lean

import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicLevel

theorem AutomorphicForm.IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq
    {F : Type} [Field F] [NumberField F] {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) :
    ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧
      ∀ (g x : AdelicGL2 (𝓞 F) F), glFin (𝓞 F) F x ∈ finiteIntegralGL2 (𝓞 F) F →
      ∀ (t : AdeleRing (𝓞 F) F), adeleArch (𝓞 F) F t = 0 →
        adeleFin (𝓞 F) F t ∈ idealBall (𝓞 F) F 𝔫 →
          φ (g * (x⁻¹ * unipotentGL2 t * x)) = φ g := by sorry
