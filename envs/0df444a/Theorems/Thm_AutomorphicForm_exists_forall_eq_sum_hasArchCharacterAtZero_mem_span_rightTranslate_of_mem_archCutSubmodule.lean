-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_eq_sum_hasArchCharacterAtZero_mem_span_rightTranslate_of_mem_archCutSubmodule
-- name    : AutomorphicForm.exists_forall_eq_sum_hasArchCharacterAtZero_mem_span_rightTranslate_of_mem_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/3b25e894-895b-51a1-9ee3-d0e7b7ec56c6
-- title:
--   Finite weight window for continuous cut vectors at a real place
-- statement:
--   Let $K$ be a number field and let $\mathrm{tys}$ be an `ArchTypeFamily K`: a number $\mathrm{card}(w)$ for each infinite place $w$ of $K$, together with, for each $w$ and each index $i < \mathrm{card}(w)$, an `ArchRepAt K w`, that is a dimension $n$ and a complex representation of `rowIsometrySubgroup₀ w.Completion` on $\mathrm{Fin}\,n \to \mathbb{C}$. The assertion is that there is an $n_0 \in \mathbb{N}$, depending only on $K$ and $\mathrm{tys}$, with the following property. Let $b : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous and lie in `archCutSubmodule K tys`, the infimum over all infinite places $w$ of the supremum over $i$ of the submodules `archTypeSubmoduleAt K w (tys.rep w i)`, and let $w$ be a real place. Then there is a family $c : \mathbb{Z} \to (\mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C})$ such that, for every $n \in \mathbb{Z}$: $c\,n$ satisfies the predicate `HasArchCharacterAt₀ K w (archWeightCharAt hw n)`, so it is a pure weight vector for the character `archWeightCharAt hw n`, the $n$-th power of `archWeightOneAt hw` (the generator character transported from $\mathbb{R}$ along the isomorphism $K_w \cong \mathbb{R}$ attached to the real place); $c\,n$ lies in the complex span of the right translates $x \mapsto b(x\cdot \mathrm{rowIsometryInclAt₀}\,K\,w\,k)$ with $k$ running over `rowIsometrySubgroup₀ w.Completion`; and $c\,n = 0$ whenever $|n| > n_0$. Finally $b = \sum_{n = -n_0}^{n_0} c\,n$.
--
--   This is the finite $K$-type (weight) decomposition at a real place: a continuous vector cut out by a fixed family of archimedean types decomposes as a finite sum of pure $\mathrm{SO}(2)$-weight components lying in the span of its own right translates, with the weight window bounded in terms of the type family alone. It is used in the estimate [`AutomorphicForm.exists_forall_eLpNorm_archDerivAt_E_sub_Fm_foldr_le_of_mem_archCutSubmodule`](thm.html#AutomorphicForm.exists_forall_eLpNorm_archDerivAt_E_sub_Fm_foldr_le_of_mem_archCutSubmodule), and rests on the finite-dimensionality and stability of the span of translates, the reduction to irreducible constituents, and the classification of continuous characters of the determinant-one row-isometry group over $\mathbb{R}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_eq_sum_hasArchCharacterAtZero_mem_span_rightTranslate_of_mem_archCutSubmodule.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_eq_sum_hasArchCharacterAtZero_mem_span_rightTranslate_of_mem_archCutSubmodule
    (K : Type) [Field K] [NumberField K]
    (tys : ArchTypeFamily K) :
    ∃ n₀ : ℕ,
      ∀ b : AdelicGL2 (𝓞 K) K → ℂ, Continuous b → b ∈ archCutSubmodule K tys →
        ∀ (w : InfinitePlace K) (hw : w.IsReal),
          ∃ c : ℤ → AdelicGL2 (𝓞 K) K → ℂ,
            (∀ n : ℤ, HasArchCharacterAt₀ K w (archWeightCharAt hw n) (c n)) ∧
            (∀ n : ℤ, c n ∈ Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
              rightTranslate K (rowIsometryInclAt₀ K w k) b)) ∧
            (∀ n : ℤ, (n₀ : ℤ) < |n| → c n = 0) ∧
            b = ∑ n ∈ Finset.Icc (-(n₀ : ℤ)) n₀, c n := by sorry
