-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_IsCuspConstituent_localSpaceAt_cyclic_finite_fixed_smooth_of_hasMultiplicityOneAt
-- name    : AutomorphicForm.CuspidalConstituent.IsCuspConstituent.localSpaceAt_cyclic_finite_fixed_smooth_of_hasMultiplicityOneAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/c4eb43de-762b-5337-86a0-6e21ac7c2e4b
-- title:
--   Local Whittaker space at p: irreducible, admissible, smooth
-- statement:
--   Fix a homomorphism $\xi$ from the subgroup $Z$ of ideles pinned by `productionPinsGeneral ℚ` to $\mathbb{C}^\times$, and a $\mathbb{C}$-submodule $V$ of the space of functions on $\mathrm{GL}_2$ of the adele ring of $\mathbb{Q}$ which is a cuspidal constituent for these data: $V$ is a cusp subrepresentation (contained in the $K$-finite cuspidal submodule cut out by $\xi$, stable under right translation by finite-adelic elements and by the archimedean row-isometry subgroups, and stable under right convolution by factorizable archimedeally bi-finite test functions), $V \neq 0$, and every cusp subrepresentation contained in $V$ is $0$ or $V$. Let $p$ be a nonzero prime of $\mathcal{O}_{\mathbb{Q}}$, let $\rho \in V$ be such that the Whittaker coefficient of $\rho$ at $\alpha = 1$ with respect to the standard global additive character `psiQ` is not identically zero, and assume `HasMultiplicityOneAt` holds for $\rho$ at $p$ with the local character `psiV p`: every $\mathbb{C}$-linear functional on functions $\mathrm{GL}_2(\mathbb{Q}_p) \to \mathbb{C}$ which transforms by `psiV p` under right translation by upper unipotents, on the local Whittaker space of $\rho$ at $p$, agrees on that space with a constant multiple of evaluation at $1$. Then for every $\varphi \in V$, writing $S$ for the local Whittaker space of $\varphi$ at $p$, namely the $\mathbb{C}$-span of the functions $g \mapsto$ (Whittaker coefficient at $\alpha=1$ of the right translate $x \mapsto \varphi(xh)$, evaluated at the image of $g$ under the local-to-adelic embedding) for $h$ ranging over adelic $\mathrm{GL}_2$: (i) for every nonzero $W_0 \in S$, every $W \in S$ lies in the span of the right translates $g \mapsto W_0(gh)$, $h \in \mathrm{GL}_2(\mathbb{Q}_p)$; (ii) for every open subgroup $U \le \mathrm{GL}_2(\mathbb{Q}_p)$ there is a finite set $B$ of functions on $\mathrm{GL}_2(\mathbb{Q}_p)$ such that every $W \in S$ invariant under right translation by $U$ lies in the span of $B$; (iii) every $W \in S$ is invariant under right translation by some open subgroup.
--
--   This is the local statement, at a finite place $p$, that the Whittaker model attached to a vector in a cuspidal constituent is an irreducible, admissible, smooth representation of $\mathrm{GL}_2(\mathbb{Q}_p)$ under right translation, irreducibility being expressed by the cyclicity of every nonzero vector. It is used in the Langlands–Tunnell part of the development, where local components of the automorphic representations attached to weight-one forms and to Casimir eigenvectors are analysed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_IsCuspConstituent_localSpaceAt_cyclic_finite_fixed_smooth_of_hasMultiplicityOneAt.lean

import Definitions.Def_AutomorphicForm_WhittakerModelMultiplicityOne
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem
AutomorphicForm.CuspidalConstituent.IsCuspConstituent.localSpaceAt_cyclic_finite_fixed_smooth_of_hasMultiplicityOneAt
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hV : CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ V) (p : HeightOneSpectrum (𝓞 ℚ))
    (ρ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hρV : ρ ∈ V)
    (hρW : whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ ρ 1 ≠ 0)
    (hρ1 : AutomorphicForm.WhittakerModel.HasMultiplicityOneAt ℚ (productionPinsGeneral ℚ)
      NumberField.StandardAddChar.psiQ ρ p (NumberField.StandardAddChar.psiV p))
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφV : φ ∈ V) :
    (∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p
      φ, W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
      NumberField.StandardAddChar.psiQ p φ, W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
    (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) → ∃ B :
      Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ
      (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p φ, (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
    (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p
      φ, ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈
      U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) := by sorry
