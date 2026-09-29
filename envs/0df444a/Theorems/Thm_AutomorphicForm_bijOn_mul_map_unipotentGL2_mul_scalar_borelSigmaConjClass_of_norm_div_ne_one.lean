-- Prove2me | Theorems.Thm_AutomorphicForm_bijOn_mul_map_unipotentGL2_mul_scalar_borelSigmaConjClass_of_norm_div_ne_one
-- name    : AutomorphicForm.bijOn_mul_map_unipotentGL2_mul_scalar_borelSigmaConjClass_of_norm_div_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/6a99be12-f64a-59dd-ab6c-47abc779f751
-- title:
--   Parametrisation of a regular twisted conjugacy class in GL₂
-- statement:
--   Let $K \subseteq L$ be fields with $L$ a finite-dimensional $K$-algebra, let $\sigma$ be a $K$-algebra automorphism of $L$, acting on $\mathrm{GL}_2(L)$ entrywise through `Matrix.GeneralLinearGroup.map` applied to the underlying ring homomorphism, and let $t' \in \mathrm{GL}_2(L)$ have vanishing $(1,0)$ and $(0,1)$ entries, i.e. be diagonal, with $\mathrm{N}_{L/K}(t'_{00}/t'_{11}) \neq 1$. Let $J \subseteq \mathrm{GL}_2(L)$ be a set characterised by: $\gamma \in J$ if and only if there is $b \in \mathrm{GL}_2(L)$ with $b_{10} = 0$ such that $t'^{-1}\bigl(b^{-1}\gamma\,\sigma(b)\bigr)$ lies in the centre of $\mathrm{GL}_2(L)$. Let $M$ be a subgroup characterised by: $m \in M$ if and only if $m_{10} = m_{01} = 0$ and $t'^{-1}\bigl(m\,t'\,\sigma(m)^{-1}\bigr)$ is central. Let $a : \kappa \to \mathrm{GL}_2(L)$ be a family of matrices, each with vanishing $(1,0)$ and $(0,1)$ entries, such that every $d \in \mathrm{GL}_2(L)$ with $d_{10} = d_{01} = 0$ satisfies $(a_j)^{-1}d \in M$ for exactly one $j$. Then the map $$(j,\zeta,s) \longmapsto a_j\,t'\;\sigma\!\left(\begin{pmatrix}1 & s\\ 0 & 1\end{pmatrix}\right)\,\zeta I_2\;\sigma(a_j)^{-1}$$ from $\kappa \times L^\times \times L$ to $\mathrm{GL}_2(L)$ is a bijection from the whole of $\kappa \times L^\times \times L$ onto $J$: it takes values in $J$, is injective, and its image is all of $J$.
--
--   This is the combinatorial parametrisation of the upper-triangular part of a regular ($\mathrm{N}_{L/K}(t'_{00}/t'_{11}) \neq 1$) twisted conjugacy class in $\mathrm{GL}_2(L)$, saturated by the centre, by representatives of the diagonal torus modulo the twisted stabiliser $M$, the central scalars, and the unipotent parameter $s \in L$. It is used in the computation of the constant term of such a class, where the resulting integral is regrouped as a sum over the representatives $a_j$ of integrals over $L^\times \times L$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_bijOn_mul_map_unipotentGL2_mul_scalar_borelSigmaConjClass_of_norm_div_ne_one.lean

import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.bijOn_mul_map_unipotentGL2_mul_scalar_borelSigmaConjClass_of_norm_div_ne_one
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) (t' : GL (Fin 2) L)
    (ht'u : (t' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht'l : (t' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0 / (t' : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (J : Set (GL (Fin 2) L))
    (hJ : ∀ γ, γ ∈ J ↔ ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      t'⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L))
    (M : Subgroup (GL (Fin 2) L))
    (hM : ∀ m, m ∈ M ↔ ((m : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (m : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      t'⁻¹ * (m * t' * (Matrix.GeneralLinearGroup.map (σ : L →+* L) m)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {κ : Type*} (a : κ → GL (Fin 2) L)
    (haD : ∀ j, ((a j : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      ((a j : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (ha : ∀ d : GL (Fin 2) L, (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (d : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
      ∃! j, (a j)⁻¹ * d ∈ M) :
    Set.BijOn (fun p : κ × Lˣ × L =>
        a p.1 * t' * Matrix.GeneralLinearGroup.map (σ : L →+* L) (AutomorphicForm.unipotentGL2 p.2.2) *
          Matrix.GeneralLinearGroup.scalar (Fin 2) p.2.1 * (Matrix.GeneralLinearGroup.map (σ : L →+* L) (a p.1))⁻¹)
      Set.univ J := by sorry
