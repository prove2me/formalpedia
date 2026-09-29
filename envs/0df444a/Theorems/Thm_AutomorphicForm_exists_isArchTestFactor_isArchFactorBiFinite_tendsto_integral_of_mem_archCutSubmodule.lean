-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule
-- name    : AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/8c34963e-db76-5ba1-980e-200198c6d1ea
-- title:
--   Archimedean approximate identity of prescribed archimedean types
-- statement:
--   Let $L$ be a number field and let $\mathrm{tys}$ be an `ArchTypeFamily` for $L$: a function assigning to each infinite place $w$ of $L$ a natural number $\mathrm{card}\,w$ together with, for each $i < \mathrm{card}\,w$, an `ArchRepAt` datum at $w$, that is a dimension $n$ and a complex representation $\rho$ of the group `rowIsometrySubgroup₀` of $w$'s completion on $\mathbb{C}^n$. Let $f : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ be continuous and lie in `archCutSubmodule L tys`, the infimum over all infinite places $w$ of the sum over $i < \mathrm{card}\,w$ of the type submodules `typeSubmodule (rowIsometryInclAt₀ L w) (tys.rep w i).ρ` inside the functions on $\mathrm{GL}_2(\mathbb{A}_L)$. Then there exists a sequence $fa : \mathbb{N} \to (\mathrm{GL}_2(\mathbb{A}_{L,\infty}) \to \mathbb{C})$ such that each $fa_n$ is an `IsArchTestFactor`, i.e. $fa_n g = \Phi(\text{archEntries } g)$ for some $\Phi$ that is $C^\infty$ over $\mathbb{R}$ on matrices over the mixed space of $L$, where `archEntries` transports the entries of $g$ through the identification of the infinite adele ring with the mixed space, and $fa_n$ has compact support; each $fa_n$ is moreover `IsArchFactorBiFinite` for $\mathrm{tys}$, meaning $x \mapsto fa_n(x^{-1})$ lies in `archFactorCutSubmodule L tys` and $fa_n$ lies in `archFactorDualCutSubmodule L tys`, the corresponding infima over infinite places of sums of the (respectively dual) type submodules of functions on $\mathrm{GL}_2(\mathbb{A}_{L,\infty})$ attached to the representations $(\mathrm{tys}.\mathrm{rep}\,w\,i).\rho$; and for every $g \in \mathrm{GL}_2(\mathbb{A}_L)$ one has $\int f\big(g \cdot \iota(y)\big)\, fa_n(y)\, d\mu(y) \to f(g)$ as $n \to \infty$, where $\iota$ is `adelicArchGLIncl`, the embedding of $\mathrm{GL}_2(\mathbb{A}_{L,\infty})$ into $\mathrm{GL}_2(\mathbb{A}_L)$ with trivial finite component, and $\mu$ is the Haar measure `archHaarK L` for the Borel structure `glBorelOf`.
--
--   This is the archimedean approximate-identity step: a continuous function on $\mathrm{GL}_2(\mathbb{A}_L)$ whose behaviour under the maximal compact subgroups at the infinite places is constrained to the given finite list of types is recovered, in the limit, by right convolution with smooth compactly supported functions on $\mathrm{GL}_2(\mathbb{A}_{L,\infty})$ that are finite on both sides of the same types. It is used in the construction of factorizable test functions of a given type and of principal level, and in the extraction of an irreducible constituent from the span of translates of an automorphic form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule
    (L : Type) [Field L] [NumberField L] (tys : ArchTypeFamily L)
    (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f) (harch : f ∈ archCutSubmodule L tys) :
    ∃ fa : ℕ → (GL (Fin 2) (InfiniteAdeleRing L) → ℂ),
      (∀ n, IsArchTestFactor L (fa n) ∧ IsArchFactorBiFinite L tys (fa n)) ∧
      ∀ g, Filter.Tendsto
        (fun n => letI := glBorelOf (InfiniteAdeleRing L)
          ∫ y, f (g * adelicArchGLIncl L y) * fa n y ∂(archHaarK L))
        Filter.atTop (nhds (f g)) := by sorry
