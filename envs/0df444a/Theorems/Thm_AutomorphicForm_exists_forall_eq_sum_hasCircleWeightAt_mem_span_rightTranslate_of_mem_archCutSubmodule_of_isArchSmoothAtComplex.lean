-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_eq_sum_hasCircleWeightAt_mem_span_rightTranslate_of_mem_archCutSubmodule_of_isArchSmoothAtComplex
-- name    : AutomorphicForm.exists_forall_eq_sum_hasCircleWeightAt_mem_span_rightTranslate_of_mem_archCutSubmodule_of_isArchSmoothAtComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/1672155c-631c-5933-8cc9-de5103cd6f6d
-- title:
--   Finite circle-weight window of a cut vector at a complex place
-- statement:
--   Let $K$ be a number field and let `tys` be an `ArchTypeFamily K`: a cardinality function $w \mapsto \mathrm{card}(w)$ on the infinite places of $K$ together with, for each $w$, a family $\mathrm{rep}(w) : \mathrm{Fin}(\mathrm{card}(w)) \to$ `ArchRepAt K w`, each member of which consists of an integer $n$ and a representation of the group `rowIsometrySubgroup₀ w.Completion` on $\mathbb{C}^n$. The assertion is that there is an $n_0 \in \mathbb{N}$, depending only on $K$ and `tys`, with the following property. Let $b : GL_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous and lie in `archCutSubmodule K tys`, that is in $\bigsqcap_{w} \bigsqcup_{i}$ `archTypeSubmoduleAt K w (tys.rep w i)`, the intersection over all infinite places $w$ of the sum over $i$ of the submodules `typeSubmodule (rowIsometryInclAt₀ K w) (tys.rep w i).ρ`. Let $w$ be an infinite place with $w$ complex, and assume `IsArchSmoothAtComplex hw b`: for every $g \in GL_2(\mathbb{A}_K)$ the function $e \mapsto b(g \cdot \mathrm{archComplexLiftAt}\ hw\ e)$ is $C^\infty$ in the real sense on the set of $2 \times 2$ complex matrices $e$ with $\det e \neq 0$. Then there is a family $c : \mathbb{Z} \to (GL_2(\mathbb{A}_K) \to \mathbb{C})$ such that: (i) each $c_n$ has circle weight $n$ at $w$, i.e. $c_n(g \cdot \mathrm{archCircleAt}\ hw\ \zeta) = \zeta^n c_n(g)$ for all $g$ and all units $\zeta$ of $\mathbb{C}$ with $\lVert \zeta \rVert = 1$; (ii) each $c_n$ lies in the $\mathbb{C}$-span of the right translates $x \mapsto b(x \cdot \mathrm{rowIsometryInclAt₀}\ K\ w\ k)$ as $k$ ranges over `rowIsometrySubgroup₀ w.Completion`; (iii) $c_n = 0$ whenever $|n| > n_0$; and (iv) $b = \sum_{n = -n_0}^{n_0} c_n$.
--
--   This is the decomposition of a vector cut out by a family of archimedean types into its weight components for the circle subgroup at a complex place, with a bound on the occurring weights that is uniform in the vector: the analogue, at a complex place, of a finite Fourier expansion along the diagonal circle in $SU(2)$. It feeds the $L^p$-norm estimates for the archimedean derivatives `archDerivAtComplex` of cut vectors, via the finite-dimensionality and $SU(2)$-stability of the span of the $SU(2)$-translates of such a vector.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_eq_sum_hasCircleWeightAt_mem_span_rightTranslate_of_mem_archCutSubmodule_of_isArchSmoothAtComplex.lean

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
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_eq_sum_hasCircleWeightAt_mem_span_rightTranslate_of_mem_archCutSubmodule_of_isArchSmoothAtComplex
    (K : Type) [Field K] [NumberField K]
    (tys : ArchTypeFamily K) :
    ∃ n₀ : ℕ,
      ∀ b : AdelicGL2 (𝓞 K) K → ℂ, Continuous b → b ∈ archCutSubmodule K tys →
        ∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw b →
          ∃ c : ℤ → AdelicGL2 (𝓞 K) K → ℂ,
            (∀ n : ℤ, HasCircleWeightAt hw n (c n)) ∧
            (∀ n : ℤ, c n ∈ Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
              rightTranslate K (rowIsometryInclAt₀ K w k) b)) ∧
            (∀ n : ℤ, (n₀ : ℤ) < |n| → c n = 0) ∧
            b = ∑ n ∈ Finset.Icc (-(n₀ : ℤ)) n₀, c n := by sorry
