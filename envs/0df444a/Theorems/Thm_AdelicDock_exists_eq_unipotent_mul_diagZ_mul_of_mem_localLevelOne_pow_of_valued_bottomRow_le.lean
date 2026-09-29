-- Prove2me | Theorems.Thm_AdelicDock_exists_eq_unipotent_mul_diagZ_mul_of_mem_localLevelOne_pow_of_valued_bottomRow_le
-- name    : AdelicDock.exists_eq_unipotent_mul_diagZ_mul_of_mem_localLevelOne_pow_of_valued_bottomRow_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/6327812a-84ae-51a0-888f-92e2e19d1604
-- title:
--   Bottom-row cell decomposition modulo K₁(𝔭^m)
-- statement:
--   Let $F$ be a number field with ring of integers $\mathcal O_F$, let $v$ be a height-one prime of $\mathcal O_F$, and write $F_v$ for the $v$-adic completion with its valuation $\mathrm{Valued.v}$ taking values in $\mathbb{Z}_{\le}$-exponentials. Let $\varpi$ be an element of the valuation ring of $F_v$ whose image in $F_v$ is nonzero and has valuation $\exp(-1)$, let $m$ be a natural number with $m \ge 1$, and let $g \in \mathrm{GL}_2(F_v)$ be such that its bottom row $(c,d)$ satisfies $\mathrm{v}(c) \le \exp(-m)$ and $\mathrm{v}(d-1) \le \exp(-m)$. Then there exist $x \in F_v$, an integer $n$, and $k \in \mathrm{GL}_2(F_v)$ such that: $k$ lies in `localLevelOne (𝓞 F) F v (v.asIdeal ^ m)`, that is, the image of $k$ under `localEmbed` in $\mathrm{GL}_2$ of the finite adele ring of $F$ lies in `AdelicLevel.finiteLevelOne` for the ideal $v^m$, so that both that adelic matrix and its inverse satisfy the predicate `IsLevelOneMatrix` at level $v^m$; moreover $$g = \begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}\begin{pmatrix} \varpi^{n} & 0 \\ 0 & 1\end{pmatrix} k,$$ the middle factor being `diagZ` with integer exponent $n$, and $\mathrm{v}(\det g) = \exp(-n)$.
--
--   This is the local structure lemma for the cell of $\mathrm{GL}_2(F_v)$ cut out by the condition that the bottom row of $g$ be congruent to $(0,1)$ modulo $\mathfrak p^m$: such a $g$ factors as a unipotent upper-triangular matrix times a diagonal torus element $\mathrm{diag}(\varpi^n,1)$ times an element of the level group $K_1(\mathfrak p^m)$ at $v$, with the valuation of the determinant read off from $n$. It is used in the analysis of the support of adelic Whittaker/zeta integrals, being cited by [`AutomorphicForm.exists_isCompact_support_and_ideleNorm_det_eq_one_of_shellSupport_rat`](thm.html#AutomorphicForm.exists_isCompact_support_and_ideleNorm_det_eq_one_of_shellSupport_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdelicDock_exists_eq_unipotent_mul_diagZ_mul_of_mem_localLevelOne_pow_of_valued_bottomRow_le.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AdelicDock UnramifiedWhittaker

theorem AdelicDock.exists_eq_unipotent_mul_diagZ_mul_of_mem_localLevelOne_pow_of_valued_bottomRow_le
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (ϖ : v.adicCompletionIntegers F) (hπ : (ϖ : v.adicCompletion F) ≠ 0)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (m : ℕ) (hm : 1 ≤ m) (g : GL (Fin 2) (v.adicCompletion F))
    (hc : Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0) ≤ WithZero.exp (-(m : ℤ)))
    (hd : Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 - 1) ≤ WithZero.exp (-(m : ℤ))) :
    ∃ (x : v.adicCompletion F) (n : ℤ) (k : GL (Fin 2) (v.adicCompletion F)),
      k ∈ localLevelOne (𝓞 F) F v (v.asIdeal ^ m) ∧
      g = unipotent x * diagZ (ϖ : v.adicCompletion F) hπ n * k ∧
      Valued.v (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = WithZero.exp (-n) := by sorry
