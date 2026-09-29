-- Prove2me | Theorems.Thm_AutomorphicForm_exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral
-- name    : AutomorphicForm.exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/ed543379-d509-5c63-91fa-52be27f7b3ff
-- title:
--   Bruhat decomposition of integral GL₂ at a finite place
-- statement:
--   Let $F$ be a number field, let $v$ be a height-one prime of the ring of integers $\mathcal O_F$, write $F_v$ for the $v$-adic completion and $\mathcal O_v \subset F_v$ for its valuation ring, and let $g \in \mathrm{GL}_2(F_v)$ be such that all four entries of $g$ and all four entries of $g^{-1}$ lie in $\mathcal O_v$. Then there exist $\beta \in \mathrm{GL}_2(F_v)$ and $x \in F_v$ such that: the lower-left entry $\beta_{10}$ vanishes, so $\beta$ is upper triangular; all entries of $\beta$ and all entries of $\beta^{-1}$ lie in $\mathcal O_v$; $x \in \mathcal O_v$; and, with $w = \bigl(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\bigr)$ (the element `gl2Weyl`, which is its own inverse) and $n(x) = \bigl(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\bigr)$ (the element `unipotentGL2 x`, with inverse $n(-x)$), one of the two factorisations $g = \beta\, w\, n(x)$ or $g = \beta\, w\, n(x)\, w^{-1}$ holds. The second alternative rewrites as $g = \beta \bigl(\begin{smallmatrix}1&0\\x&1\end{smallmatrix}\bigr)$.
--
--   This is the two-cell Bruhat (Iwahori) decomposition $\mathrm{GL}_2(\mathcal O_v) = B(\mathcal O_v)\,w\,N(\mathcal O_v) \cup B(\mathcal O_v)\,N^-(\mathcal O_v)$, the pullback along reduction of the Bruhat decomposition of $\mathrm{GL}_2$ over the residue field, expressed with integrality of $\beta$ and $\beta^{-1}$ in place of membership in a maximal compact subgroup. It serves to reduce right translation by an integral matrix to the Borel subgroup, the unipotent radical and the Weyl element, and is used in the analysis of the Weyl intertwining integral on a flat family of local data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral.lean

import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (g : GL (Fin 2) (v.adicCompletion F))
    (_hg : ∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F)
    (_hg' : ∀ i j, ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j
      ∈ v.adicCompletionIntegers F) :
    ∃ (β : GL (Fin 2) (v.adicCompletion F)) (x : v.adicCompletion F),
      (β : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 ∧
      (∀ i j, (β : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F) ∧
      (∀ i j, ((β⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j
        ∈ v.adicCompletionIntegers F) ∧
      x ∈ v.adicCompletionIntegers F ∧
      (g = β * gl2Weyl * unipotentGL2 x ∨ g = β * gl2Weyl * unipotentGL2 x * gl2Weyl⁻¹) := by sorry
