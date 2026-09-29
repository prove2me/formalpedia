-- Prove2me | Theorems.Thm_AutomorphicForm_isClosedEmbedding_toTensorGL_and_exists_nhds_one_twistedCentralizer_iff_and_forall_isCompact_conjAe
-- name    : AutomorphicForm.isClosedEmbedding_toTensorGL_and_exists_nhds_one_twistedCentralizer_iff_and_forall_isCompact_conjAe
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/bd88591c-4d56-54c0-bb00-b5c5c03a3caa
-- title:
--   Archimedean twisted descent near a real scalar in GL₂
-- statement:
--   Let $d \in \mathbb{R}^\times$, write $\iota =$ `toTensorGL ℝ ℂ ℝ` for the group homomorphism $GL_2(\mathbb{R}) \to GL_2(\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R})$ obtained by applying the right inclusion $\mathbb{R} \to \mathbb{C} \otimes_{\mathbb{R}} \mathbb{R}$ entrywise, and write $\sigma =$ `sigmaGL ℝ ℂ ℝ Complex.conjAe` for the entrywise action of $\mathrm{conj} \otimes \mathrm{id}$ on $\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R}$. The assertion is the conjunction of: (i) $\iota$ is a closed embedding for the topologies on the two general linear groups; and (ii) there exists a neighbourhood $U$ of $1$ in $GL_2(\mathbb{R})$ such that, setting $\delta_t = \iota(t \cdot d I_2)$ for $t \in U$, both of the following hold. First, for every $t \in U$ and every $x \in GL_2(\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R})$, the twisted centraliser condition $x \delta_t (\sigma x)^{-1} = \delta_t$ holds if and only if $x = \iota(m)$ for some $m \in GL_2(\mathbb{R})$ commuting with $t$. Second, for every compact $C \subseteq GL_2(\mathbb{C})$ there is a compact $K \subseteq GL_2(\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R})$ such that, for all $t \in U$ and all $x$, if the image of $x^{-1} \delta_t \sigma(x)$ under the entrywise isomorphism $\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R} \cong \mathbb{C}$ (given by `Algebra.TensorProduct.rid ℝ ℝ ℂ`) lies in $C$, then $x = \iota(m) k$ for some $m \in GL_2(\mathbb{R})$ and some $k \in K$.
--
--   This packages the archimedean input for twisted descent at a scalar element: the real points form a closed subgroup, the $\sigma$-twisted centraliser of $\iota(t \cdot d I_2)$ collapses to the ordinary centraliser of $t$ inside $GL_2(\mathbb{R})$ for $t$ near $1$, and twisted conjugation into a compact set is possible only from a set compact modulo left translation by $\iota(GL_2(\mathbb{R}))$, uniformly in $t$ near $1$. It is used in the construction of twisted orbital integrals and of twisted section functions for complex conjugation, feeding the comparison of twisted and ordinary orbital integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isClosedEmbedding_toTensorGL_and_exists_nhds_one_twistedCentralizer_iff_and_forall_isCompact_conjAe.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isClosedEmbedding_toTensorGL_and_exists_nhds_one_twistedCentralizer_iff_and_forall_isCompact_conjAe
    (d : ℝˣ) :
    Topology.IsClosedEmbedding (toTensorGL ℝ ℂ ℝ) ∧
    ∃ U ∈ nhds (1 : GL (Fin 2) ℝ),
      (∀ t ∈ U, ∀ x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        x ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe
            (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)) ↔
          ∃ m : GL (Fin 2) ℝ, m ∈ Subgroup.centralizer ({t} : Set (GL (Fin 2) ℝ)) ∧ x = toTensorGL ℝ ℂ ℝ m) ∧
      ∀ C : Set (GL (Fin 2) ℂ), IsCompact C →
        ∃ K : Set (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), IsCompact K ∧
          ∀ t ∈ U, ∀ x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
            (Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
              (x⁻¹ * toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d) *
                sigmaGL ℝ ℂ ℝ Complex.conjAe x) : GL (Fin 2) ℂ) ∈ C →
              ∃ (m : GL (Fin 2) ℝ) (k : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), k ∈ K ∧ x = toTensorGL ℝ ℂ ℝ m * k := by sorry
