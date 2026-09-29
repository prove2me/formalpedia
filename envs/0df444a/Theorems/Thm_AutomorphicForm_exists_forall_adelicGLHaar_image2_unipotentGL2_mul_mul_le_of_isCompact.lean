-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact
-- name    : AutomorphicForm.exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/ec40496c-32df-50e6-9736-b5a33963dd11
-- title:
--   Uniform Haar bound for unipotent sweeps over a centre-cut Siegel set
-- statement:
--   Let $K$ be a number field, let $c', u', d_1', d_2'$ be real numbers with $c' > 0$, and let $C \subseteq \mathrm{GL}_2(\mathbb{A}_K)$ be a compact set. The assertion is that there exists a real number $M_0 \ge 0$ with the following property: for every $s$ in the centre-cut Siegel set `centreCutSiegelSet K c' u' d₁' d₂'` — that is, every $s \in \mathrm{GL}_2(\mathbb{A}_K)$ whose finite component `glFin` lies in the subgroup `finiteIntegralGL2` (the group `finiteLevelZero` at the unit ideal $\top$), whose archimedean component satisfies, at every infinite place $w$ of $K$, $c' \le \|\det\|/\mathrm{rowNormSq}$, $\mathrm{topNormSq}/\mathrm{rowNormSq} - (\|\det\|/\mathrm{rowNormSq})^2 \le u'^2$ and $\|\det\| \in [d_1', d_2']$, all norms and quadratic quantities being those of the matrix at $w$ — the Haar measure `adelicGLHaar` of $\mathrm{GL}_2(\mathbb{A}_K)$ (for the Borel structure `glBorel`) assigns to the set $\{\, n(t)\, s\, c : t \in \overline{B},\ c \in C \,\}$ a value at most $\mathrm{ofReal}\, M_0$. Here $n(t) = \begin{pmatrix} 1 & t \\ 0 & 1\end{pmatrix}$, and $\overline{B}$ is the closure of the adelic box of $K$, the set of adeles whose infinite part lies in the preimage of the fundamental domain of the lattice basis of $K$ and whose finite part is integral at every finite place. The constant $M_0$ depends on $K$, the four parameters and $C$, but not on $s$.
--
--   This is the uniform volume estimate from reduction theory of $\mathrm{GL}_2$ over a number field: one Haar bound for the sets swept out from a point of a Siegel set by unipotent translations from the adelic box on the left and a fixed compact set on the right, valid uniformly along the Siegel set thanks to the height floor $c' > 0$. It feeds the bound on convolutions of cusp forms with compactly supported kernels along the Siegel set used in [`AutomorphicForm.exists_norm_rightConv_mul_le_mul_inv_archHeight_pow_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre`](thm.html#AutomorphicForm.exists_norm_rightConv_mul_le_mul_inv_archHeight_pow_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact.lean

import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicBox NumberField.AdelicHaar AutomorphicForm AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact (K : Type) [Field K] [NumberField K]
    (c' u' d₁' d₂' : ℝ) (hc' : 0 < c')
    {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ s ∈ centreCutSiegelSet K c' u' d₁' d₂',
      adelicGLHaar (Fin 2) (𝓞 K) K
          (Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
            unipotentGL2 t * s * c) (closure (adelicBox K)) C)
        ≤ ENNReal.ofReal M₀ := by sorry
