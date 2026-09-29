-- Prove2me | Theorems.Thm_AutomorphicForm_exists_orthonormal_maximalCompactHaar_basis_of_finiteDimensional
-- name    : AutomorphicForm.exists_orthonormal_maximalCompactHaar_basis_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/7f51b491-88df-5cf3-945c-3532ff673136
-- title:
--   Orthonormal basis for the maximal compact K-pairing
-- statement:
--   Let $K$ be a number field, and write $G = \mathrm{GL}_2(\mathbb A_K)$ for the general linear group of rank $2$ over the adele ring of $\mathcal O_K$ in $K$, equipped with its Borel measurable structure. Inside $G$ sits the subgroup [`AutomorphicForm.adelicMaximalCompact K`](def/AutomorphicForm_AdelicMaximalCompact.html#L19) consisting of those $k$ whose finite component lies in `finiteIntegralGL2` and whose archimedean component at every infinite place $w$ of $K$ is a row isometry; [`AutomorphicForm.maximalCompactHaar K`](def/AutomorphicForm_AdelicMaximalCompact.html#L208) is the Haar measure on this subgroup normalised so that the whole group has mass $1$. Let $V$ be a $\mathbb C$-submodule of the space of all functions $G \to \mathbb C$, finite-dimensional over $\mathbb C$, such that (i) every $\varphi \in V$ is continuous and (ii) the form is definite on $V$: if $\varphi \in V$ and $\int_{\mathbf K} \varphi(k)\overline{\varphi(k)}\,dk = 0$, then $\varphi = 0$. The assertion is that there exist $n \in \mathbb N$ and $b : \mathrm{Fin}\,n \to (G \to \mathbb C)$ with $b_i \in V$ for all $i$, with $\int_{\mathbf K} b_i(k)\overline{b_j(k)}\,dk = \delta_{ij}$ for all $i, j$, and with every $\varphi \in V$ lying in the $\mathbb C$-span of the range of $b$; together with $b_i \in V$ this makes that span equal to $V$.
--
--   This is the existence of a $\mathbf K$-orthonormal basis of a finite-dimensional space of continuous functions on $\mathrm{GL}_2(\mathbb A_K)$ for the pairing given by integration over the standard maximal compact subgroup. It is used in the construction of countable orthonormal families of flat induced sections at a fixed principal level, where definiteness of the pairing comes from the fact that such a section is determined by its restriction to the maximal compact subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_orthonormal_maximalCompactHaar_basis_of_finiteDimensional.lean

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_orthonormal_maximalCompactHaar_basis_of_finiteDimensional
    (K : Type) [Field K] [NumberField K]
    (V : Submodule ℂ (AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ)) [FiniteDimensional ℂ V]
    (hcont : ∀ φ ∈ V, Continuous φ)
    (hdef : ∀ φ ∈ V,
      (∫ k, φ (k : AutomorphicForm.AdelicGL2 (𝓞 K) K) * conj (φ (k : AutomorphicForm.AdelicGL2 (𝓞 K) K))
        ∂(AutomorphicForm.maximalCompactHaar K)) = 0 → φ = 0) :
    ∃ (n : ℕ) (b : Fin n → (AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ)),
      (∀ i, b i ∈ V) ∧
      (∀ i j, ∫ k, b i (k : AutomorphicForm.AdelicGL2 (𝓞 K) K) * conj (b j (k : AutomorphicForm.AdelicGL2 (𝓞 K) K))
          ∂(AutomorphicForm.maximalCompactHaar K) = if i = j then 1 else 0) ∧
      (∀ φ ∈ V, φ ∈ Submodule.span ℂ (Set.range b)) := by sorry
