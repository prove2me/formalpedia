-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates
-- name    : AutomorphicForm.exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/b346f3f7-3942-55d9-bab0-6d222be3dc50
-- title:
--   Continuous part of a finite family of K-types
-- statement:
--   Let $K$ be a compact topological group, let $I$ be a finite index type, and for each $i \in I$ let $W_i$ be a finite-dimensional complex vector space carrying a representation $\rho_i$ of $K$ (an abstract homomorphism $K \to \mathrm{GL}(W_i)$; no continuity is assumed). Then there exist $n \in \mathbb{N}$ and a multiplicative map $\rho^{c} \colon K \to M_n(\mathbb{C})$ which is continuous, with the following property for every group $G$ and every injective group homomorphism $\iota \colon K \to G$. Write $\mathcal{T} = \bigsqcup_i \mathtt{typeSubmodule}\,\iota\,\rho_i$ for the supremum, inside the $\mathbb{C}$-module $\mathbb{C}^{G}$, of the submodules $\mathtt{typeSubmodule}\,\iota\,\rho_i$, each of which is by definition the $\mathbb{C}$-span of the set of functions lying in the range of some $\mathbb{C}$-linear $S \colon W_i \to \mathbb{C}^{G}$ satisfying $S(\rho_i(k)v)(x) = S(v)(x\,\iota(k))$ for all $k \in K$, $v \in W_i$, $x \in G$. Then: (1) every $\mathbb{C}$-linear $T \colon \mathbb{C}^{n} \to \mathbb{C}^{G}$ satisfying $T(\rho^{c}(k)x) = \bigl(y \mapsto T(x)(y\,\iota(k))\bigr)$ for all $k \in K$ and $x \in \mathbb{C}^{n}$ takes all its values $T(x)$ in $\mathcal{T}$; and (2) for every $f \in \mathcal{T}$ such that for each $y \in G$ the orbit map $k \mapsto f(y\,\iota(k))$ is continuous on $K$, there are $m \in \mathbb{N}$ and a $\mathbb{C}$-linear $T \colon (\mathbb{C}^{n})^{m} \to \mathbb{C}^{G}$ with $T\bigl(j \mapsto \rho^{c}(k)x_j\bigr) = \bigl(y \mapsto T(x)(y\,\iota(k))\bigr)$ for all $k$ and $x$, whose range is exactly the $\mathbb{C}$-span of the translates $\{\,y \mapsto f(y\,\iota(k)) : k \in K\,\}$.
--
--   This isolates the continuous part of the family $(\rho_i)_{i \in I}$ as it is seen by functions on $G$ of those types: a single continuous matrix representation $\rho^{c}$ whose equivariant images lie in the sum of the type pieces, and which conversely carries the span of the translates of any type function with continuous orbit maps. It is used in the construction of the archimedean type projectors for the cuspidal spectrum, and in the associated statements producing continuous idempotent kernels on a maximal compact subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    {I : Type*} [Finite I] {W : I → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    [∀ i, Module.Finite ℂ (W i)] (ρ : ∀ i, Representation ℂ K (W i)) :
    ∃ (n : ℕ) (ρc : K →* Matrix (Fin n) (Fin n) ℂ), Continuous ρc ∧
      ∀ (G : Type*) [Group G] (ι : K →* G), Function.Injective ι →
        (∀ (T : (Fin n → ℂ) →ₗ[ℂ] (G → ℂ)),
          (∀ (k : K) (x : Fin n → ℂ), T ((ρc k).mulVec x) = fun y => T x (y * ι k)) →
          ∀ x : Fin n → ℂ, T x ∈ ⨆ i, typeSubmodule ι (ρ i)) ∧
        (∀ f ∈ ⨆ i, typeSubmodule ι (ρ i), (∀ y : G, Continuous fun k : K => f (y * ι k)) →
          ∃ (m : ℕ) (T : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] (G → ℂ)),
            (∀ (k : K) (x : Fin m → (Fin n → ℂ)), T (fun j => (ρc k).mulVec (x j)) = fun y => T x (y * ι k)) ∧
            LinearMap.range T = Submodule.span ℂ (Set.range fun k : K => fun y : G => f (y * ι k))) := by sorry
