-- Prove2me | Theorems.Thm_AutomorphicForm_exists_nhds_one_forall_isCompact_exists_eq_toTensorGL_mul_of_conjAe_twistedConj_mem
-- name    : AutomorphicForm.exists_nhds_one_forall_isCompact_exists_eq_toTensorGL_mul_of_conjAe_twistedConj_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/09eac663-cf67-5557-95be-2315c0e29566
-- title:
--   Uniform properness of twisted conjugation near real scalars
-- statement:
--   Let $d$ be a unit of $\mathbb{R}$. Write $\iota =$ `toTensorGL ℝ ℂ ℝ` for the group homomorphism $GL_2(\mathbb{R}) \to GL_2(\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R})$ obtained by applying the right inclusion $a \mapsto 1 \otimes a$ entrywise, $\sigma =$ `sigmaGL ℝ ℂ ℝ Complex.conjAe` for the automorphism of $GL_2(\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R})$ obtained by applying complex conjugation on the left tensor factor entrywise, and let $GL_2(\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R}) \to GL_2(\mathbb{C})$ be the isomorphism induced entrywise by `Algebra.TensorProduct.rid ℝ ℝ ℂ`, i.e. $z \otimes r \mapsto rz$. The assertion is that there exists a neighbourhood $U$ of $1$ in $GL_2(\mathbb{R})$ such that for every compact set $C \subseteq GL_2(\mathbb{C})$ there exists a compact set $K \subseteq GL_2(\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R})$ with the following property: for all $t \in U$ and all $x \in GL_2(\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R})$, if the image in $GL_2(\mathbb{C})$ of $x^{-1} \, \iota\!\left(t \cdot d\,I_2\right) \, \sigma(x)$ lies in $C$, then $x = \iota(m)\,k$ for some $m \in GL_2(\mathbb{R})$ and some $k \in K$. Note the order of quantifiers: the neighbourhood $U$ is chosen uniformly in $C$, while $K$ may depend on $C$.
--
--   This is a properness statement for $\sigma$-twisted conjugation in $GL_2$ of the quadratic extension $\mathbb{C}/\mathbb{R}$ at twisted conjugacy classes near the real scalar $d\,I_2$: a twisted conjugate of $\iota(t\,d\,I_2)$ staying in a compact set forces $x$ into a fixed compact set modulo the left action of $\iota(GL_2(\mathbb{R}))$, uniformly for $t$ near $1$. It supplies the third clause of [`AutomorphicForm.isClosedEmbedding_toTensorGL_and_exists_nhds_one_twistedCentralizer_iff_and_forall_isCompact_conjAe`](thm.html#AutomorphicForm.isClosedEmbedding_toTensorGL_and_exists_nhds_one_twistedCentralizer_iff_and_forall_isCompact_conjAe), used in the base-change descent for automorphic forms on $GL_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_nhds_one_forall_isCompact_exists_eq_toTensorGL_mul_of_conjAe_twistedConj_mem.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_nhds_one_forall_isCompact_exists_eq_toTensorGL_mul_of_conjAe_twistedConj_mem
    (d : ℝˣ) :
    ∃ U ∈ nhds (1 : GL (Fin 2) ℝ),
      ∀ C : Set (GL (Fin 2) ℂ), IsCompact C →
        ∃ K : Set (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), IsCompact K ∧
          ∀ t ∈ U, ∀ x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
            (Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
              (x⁻¹ * toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d) *
                sigmaGL ℝ ℂ ℝ Complex.conjAe x) : GL (Fin 2) ℂ) ∈ C →
              ∃ (m : GL (Fin 2) ℝ) (k : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), k ∈ K ∧ x = toTensorGL ℝ ℂ ℝ m * k := by sorry
