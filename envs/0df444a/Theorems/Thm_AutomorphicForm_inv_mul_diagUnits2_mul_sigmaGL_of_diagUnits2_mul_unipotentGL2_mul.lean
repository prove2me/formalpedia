-- Prove2me | Theorems.Thm_AutomorphicForm_inv_mul_diagUnits2_mul_sigmaGL_of_diagUnits2_mul_unipotentGL2_mul
-- name    : AutomorphicForm.inv_mul_diagUnits2_mul_sigmaGL_of_diagUnits2_mul_unipotentGL2_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/6ff80248-6f7e-51d9-9ed1-8436fdf2a3f5
-- title:
--   Twisted conjugate of a diagonal element in Iwasawa coordinates
-- statement:
--   Let $K \subseteq L$ be fields with $L$ a $K$-algebra, let $A$ be a commutative $K$-algebra, and write $E = L \otimes_K A$. Let $\sigma$ be a $K$-algebra automorphism of $L$, and let $\sigma_E :=$ [`AutomorphicForm.sigmaTensor K L A σ`](def/AutomorphicForm_TwistedOrbital.html#L199) denote the ring endomorphism $\sigma \otimes \mathrm{id}_A$ of $E$, with [`AutomorphicForm.sigmaGL K L A σ`](def/AutomorphicForm_TwistedOrbital.html#L202) the induced group homomorphism of $\mathrm{GL}_2(E)$ obtained by applying $\sigma_E$ to each matrix entry. For units $\alpha, \beta, a_1, a_2 \in E^{\times}$, an element $\xi \in E$ and an arbitrary $k \in \mathrm{GL}_2(E)$, write $\mathrm{diag}(x,y)$ for `diagUnits2 x y`, the invertible matrix $\begin{pmatrix} x & 0 \\ 0 & y\end{pmatrix}$ with inverse $\mathrm{diag}(x^{-1},y^{-1})$, and $n(\xi)$ for [`AutomorphicForm.unipotentGL2 ξ`](def/AutomorphicForm_ConstantTerm.html#L17), the invertible matrix $\begin{pmatrix} 1 & \xi \\ 0 & 1 \end{pmatrix}$ with inverse $n(-\xi)$. Setting $d_1 = \alpha\,\sigma_E(a_1)\,a_1^{-1}$ and $d_2 = \beta\,\sigma_E(a_2)\,a_2^{-1}$ in $E^{\times}$ (the image of $a_i$ under the induced map of unit groups), the asserted identity in $\mathrm{GL}_2(E)$ is $$(\mathrm{diag}(a_1,a_2)\,n(\xi)\,k)^{-1}\,\mathrm{diag}(\alpha,\beta)\,\sigma\bigl(\mathrm{diag}(a_1,a_2)\,n(\xi)\,k\bigr) = k^{-1}\,\mathrm{diag}(d_1,d_2)\,n\bigl(\sigma_E(\xi) - (d_2 d_1^{-1})\,\xi\bigr)\,\sigma(k),$$ where $\sigma(\cdot)$ denotes [`AutomorphicForm.sigmaGL K L A σ`](def/AutomorphicForm_TwistedOrbital.html#L202) and $d_2 d_1^{-1}$ is the image in $E$ of the corresponding unit.
--
--   This is the coordinate normalisation underlying twisted orbital integrals for $\mathrm{GL}_2$: it puts the $\sigma$-twisted conjugate of a diagonal element by a point written in Iwasawa coordinates $\mathrm{diag}(a_1,a_2)\,n(\xi)\,k$ into the normal form $k^{-1}\,\mathrm{diag}(d_1,d_2)\,n(\sigma\xi - \lambda'\xi)\,\sigma(k)$, so that the torus and unipotent variables separate. It is used in the computations of twisted orbital integrals and of semi-local test functions on the torus, where the remaining dependence on $\xi$ occurs only through $\sigma_E(\xi) - (d_2/d_1)\xi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_inv_mul_diagUnits2_mul_sigmaGL_of_diagUnits2_mul_unipotentGL2_mul.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.inv_mul_diagUnits2_mul_sigmaGL_of_diagUnits2_mul_unipotentGL2_mul
    (K L A : Type) [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L) (α β a₁ a₂ : (L ⊗[K] A)ˣ) (ξ : L ⊗[K] A) (k : GL (Fin 2) (L ⊗[K] A)) :
    (diagUnits2 a₁ a₂ * AutomorphicForm.unipotentGL2 ξ * k)⁻¹ * diagUnits2 α β *
        AutomorphicForm.sigmaGL K L A σ (diagUnits2 a₁ a₂ * AutomorphicForm.unipotentGL2 ξ * k) =
      k⁻¹ *
        (diagUnits2 (α * Units.map (AutomorphicForm.sigmaTensor K L A σ).toMonoidHom a₁ * a₁⁻¹)
            (β * Units.map (AutomorphicForm.sigmaTensor K L A σ).toMonoidHom a₂ * a₂⁻¹) *
          AutomorphicForm.unipotentGL2
            (AutomorphicForm.sigmaTensor K L A σ ξ -
              (((β * Units.map (AutomorphicForm.sigmaTensor K L A σ).toMonoidHom a₂ * a₂⁻¹) *
                  (α * Units.map (AutomorphicForm.sigmaTensor K L A σ).toMonoidHom a₁ * a₁⁻¹)⁻¹ : (L ⊗[K] A)ˣ) :
                L ⊗[K] A) * ξ)) *
        AutomorphicForm.sigmaGL K L A σ k := by sorry
