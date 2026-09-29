-- Prove2me | Theorems.Thm_AutomorphicForm_TwistedBruhat_continuous_and_hasCompactSupport_and_contDiff_integral_archWord
-- name    : AutomorphicForm.TwistedBruhat.continuous_and_hasCompactSupport_and_contDiff_integral_archWord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/c5d318c2-07e2-5c50-b7a1-15a5e01e3c23
-- title:
--   Smoothness and compact support of the archimedean unipotent integral
-- statement:
--   Let $L$ be a number field, write $L_\infty$ for its infinite adele ring and $\mathbb{L}_\infty = \mathrm{mixedSpace}\,L$ for the associated mixed space, the two being identified by the ring equivalence `InfiniteAdeleRing.ringEquiv_mixedSpace L`. Let $A$ be a continuous ring automorphism of $L_\infty$, let $\varphi : \mathrm{GL}_2(L_\infty) \to \mathbb{C}$ be an archimedean test factor, i.e. $\varphi$ has compact support and there is a $C^\infty$ function $\Phi$ on $2\times 2$ matrices over $\mathbb{L}_\infty$ with $\varphi(g) = \Phi$ applied to the entries of $g$ read in the mixed space, and let $\xi : L_\infty^\times \to \mathbb{C}$ be continuous. On the parameter space $P = L_\infty^\times \times \mathrm{GL}_2(L_\infty) \times L_\infty^\times$, equipped with Borel $\sigma$-algebras, let $\mu$ be a finite measure and $K \subseteq P$ a compact set with $\mu(K^c) = 0$. For $p = (t,k,\zeta)$ put $W(y,p) = k^{-1}\,\begin{pmatrix}1 & y t^{-1}\\ 0 & 1\end{pmatrix}\,\mathrm{diag}(A(t)t^{-1},1)\,A(\zeta)I_2\,A(k)$, where $A$ acts on $k$ entrywise. The assertion is threefold: the function $y \mapsto \int_P \xi(\zeta)\,\varphi(W(y,p))\,d\mu(p)$ on $L_\infty$ is continuous, it has compact support, and its transport to $\mathbb{L}_\infty$ along the inverse of the above ring equivalence is $C^\infty$ as a function on the real vector space $\mathbb{L}_\infty$.
--
--   This is the archimedean half of the analysis of the unipotent-type term in a twisted Bruhat decomposition: the integral over the parameter space of a smooth compactly supported test factor evaluated on a word that is affine in the unipotent variable. It is used in the construction of the transversal integral identity [`AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_eq_indicator_mul_prod_unipotentOrbitalFn_unram`](thm.html#AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_eq_indicator_mul_prod_unipotentOrbitalFn_unram), and rests on the general statement [`contDiff_top_and_hasCompactSupport_integral_comp_affine`](thm.html#contDiff_top_and_hasCompactSupport_integral_comp_affine) about integrals of smooth compactly supported functions composed with continuously varying, uniformly proper affine maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TwistedBruhat_continuous_and_hasCompactSupport_and_contDiff_integral_archWord.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm

open scoped Classical in

theorem AutomorphicForm.TwistedBruhat.continuous_and_hasCompactSupport_and_contDiff_integral_archWord
    (L : Type) [Field L] [NumberField L]
    (A : InfiniteAdeleRing L ≃+* InfiniteAdeleRing L) (hA : Continuous A)
    (φ : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφ : IsArchTestFactor L φ)
    (ξ : (InfiniteAdeleRing L)ˣ → ℂ) (hξ : Continuous ξ)
    [MeasurableSpace (InfiniteAdeleRing L)ˣ] [BorelSpace (InfiniteAdeleRing L)ˣ]
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing L))] [BorelSpace (GL (Fin 2) (InfiniteAdeleRing L))]
    (μ : Measure ((InfiniteAdeleRing L)ˣ × GL (Fin 2) (InfiniteAdeleRing L) × (InfiniteAdeleRing L)ˣ))
    [IsFiniteMeasure μ]
    (K : Set ((InfiniteAdeleRing L)ˣ × GL (Fin 2) (InfiniteAdeleRing L) × (InfiniteAdeleRing L)ˣ))
    (hK : IsCompact K) (hμK : μ Kᶜ = 0) :
    Continuous (fun y : InfiniteAdeleRing L =>
        ∫ p, ξ p.2.2 * φ (p.2.1⁻¹ * unipotentGL2 (y * ((p.1⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L)) *
          diagOne (Units.map A.toRingHom.toMonoidHom p.1 * p.1⁻¹) *
          Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map A.toRingHom.toMonoidHom p.2.2) *
          Matrix.GeneralLinearGroup.map A.toRingHom p.2.1) ∂μ) ∧
    HasCompactSupport (fun y : InfiniteAdeleRing L =>
        ∫ p, ξ p.2.2 * φ (p.2.1⁻¹ * unipotentGL2 (y * ((p.1⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L)) *
          diagOne (Units.map A.toRingHom.toMonoidHom p.1 * p.1⁻¹) *
          Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map A.toRingHom.toMonoidHom p.2.2) *
          Matrix.GeneralLinearGroup.map A.toRingHom p.2.1) ∂μ) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun x : mixedEmbedding.mixedSpace L =>
        ∫ p, ξ p.2.2 * φ (p.2.1⁻¹ *
          unipotentGL2 ((InfiniteAdeleRing.ringEquiv_mixedSpace L).symm x * ((p.1⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L)) *
          diagOne (Units.map A.toRingHom.toMonoidHom p.1 * p.1⁻¹) *
          Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map A.toRingHom.toMonoidHom p.2.2) *
          Matrix.GeneralLinearGroup.map A.toRingHom p.2.1) ∂μ) := by sorry
