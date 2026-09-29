-- Prove2me | Theorems.Thm_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_archWord_eq_zero_of_not_mem
-- name    : AutomorphicForm.TwistedBruhat.exists_isCompact_forall_archWord_eq_zero_of_not_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/7b0f12c9-9ed4-5611-9542-48ec64a045df
-- title:
--   Compact confinement of the central variable in a twisted word
-- statement:
--   Let $L$ be a number field and write $L_\infty$ for its infinite adele ring. Let $A$ be a ring automorphism of $L_\infty$ such that both $A$ and $A^{-1}$ are continuous, let $\varphi : \mathrm{GL}_2(L_\infty) \to \mathbb{C}$ have compact support, let $C_t \subseteq L_\infty^\times$ be compact and let $K \subseteq \mathrm{GL}_2(L_\infty)$ be compact. The assertion is that there is a compact set $C_\zeta \subseteq L_\infty^\times$ with the property that for every $y \in L_\infty$, every $t \in C_t$, every $k \in K$ and every unit $\zeta \notin C_\zeta$ one has
--   $$\varphi\Bigl(k^{-1}\,\begin{pmatrix}1 & y t^{-1}\\ 0 & 1\end{pmatrix}\,\begin{pmatrix}A(t)t^{-1} & 0\\ 0 & 1\end{pmatrix}\,\begin{pmatrix}A(\zeta) & 0\\ 0 & A(\zeta)\end{pmatrix}\,A(k)\Bigr) = 0 ,$$
--   where the second factor is `unipotentGL2` of $y t^{-1}$, i.e. the unipotent matrix with upper right entry $y t^{-1}$; the third is `diagOne` of the unit $A(t)t^{-1}$, i.e. $\mathrm{diag}(A(t)t^{-1},1)$; the fourth is the scalar matrix attached to the unit $A(\zeta)$; and $A(k)$ denotes the image of $k$ under the entrywise application of $A$.
--
--   This is the archimedean support estimate for the central variable in the twisted word occurring in the unfolded unipotent term: outside a compact set of central parameters $\zeta$ the integrand vanishes identically, uniformly in the unipotent parameter $y$, in $t \in C_t$ and in $k \in K$. It is used in [`AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_eq_indicator_mul_prod_unipotentOrbitalFn_unram`](thm.html#AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_eq_indicator_mul_prod_unipotentOrbitalFn_unram).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_archWord_eq_zero_of_not_mem.lean

import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm

theorem AutomorphicForm.TwistedBruhat.exists_isCompact_forall_archWord_eq_zero_of_not_mem
    (L : Type) [Field L] [NumberField L]
    (A : InfiniteAdeleRing L ≃+* InfiniteAdeleRing L) (hA : Continuous A) (hAs : Continuous A.symm)
    (φ : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφ : HasCompactSupport φ)
    (Ct : Set (InfiniteAdeleRing L)ˣ) (hCt : IsCompact Ct)
    (Kk : Set (GL (Fin 2) (InfiniteAdeleRing L))) (hKk : IsCompact Kk) :
    ∃ Cζ : Set (InfiniteAdeleRing L)ˣ, IsCompact Cζ ∧
      ∀ (y : InfiniteAdeleRing L) (t : (InfiniteAdeleRing L)ˣ) (k : GL (Fin 2) (InfiniteAdeleRing L))
        (ζ : (InfiniteAdeleRing L)ˣ), t ∈ Ct → k ∈ Kk → ζ ∉ Cζ →
        φ (k⁻¹ * unipotentGL2 (y * ((t⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L)) *
            diagOne (Units.map A.toRingHom.toMonoidHom t * t⁻¹) *
            Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map A.toRingHom.toMonoidHom ζ) *
            Matrix.GeneralLinearGroup.map A.toRingHom k) = 0 := by sorry
