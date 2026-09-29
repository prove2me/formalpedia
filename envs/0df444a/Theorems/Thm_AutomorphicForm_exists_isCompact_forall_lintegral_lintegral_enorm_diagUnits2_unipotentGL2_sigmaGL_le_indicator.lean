-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_forall_lintegral_lintegral_enorm_diagUnits2_unipotentGL2_sigmaGL_le_indicator
-- name    : AutomorphicForm.exists_isCompact_forall_lintegral_lintegral_enorm_diagUnits2_unipotentGL2_sigmaGL_le_indicator
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/925415c3-04d6-500a-aa8c-78e0529cc758
-- title:
--   Compact window for archimedean twisted orbital integrands
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ finite, let $\sigma$ be a $K$-algebra automorphism of $L$, and write $E = L \otimes_K \mathbb{A}_{K,\infty}$ for the base change of the infinite adele ring of $K$, equipped with a measurable structure that is the Borel structure of its topology. Let $\lambda$ be an additive Haar measure on $E$, and let $\kappa$ be a Haar measure, for the Borel $\sigma$-algebra, on the subgroup $\mathbf{K} \le \mathrm{GL}_2(E)$ defined as the preimage under [`AutomorphicForm.archIdentGL K L`](def/AutomorphicForm_TwistedOrbital.html#L424) (the map of general linear groups induced by the ring homomorphism $E \to \mathbb{A}_{L,\infty}$ obtained from the commutativity isomorphism and the archimedean base-change equivalence) of the intersection, over the infinite places $w$ of $L$, of the preimages under evaluation at $w$ of the subgroups of $\mathrm{GL}_2(L_w)$ consisting of those $k$ with $\|\det k\| = 1$ and $\|x k_{00} + y k_{10}\|^2 + \|x k_{01} + y k_{11}\|^2 = \|x\|^2 + \|y\|^2$ for all $x, y \in L_w$. Let $\varphi : \mathrm{GL}_2(E) \to \mathbb{C}$ have compact support and satisfy $\|\varphi(g)\| \le M$ for some real $M$ and all $g$. Then there exist $C \in [0,\infty]$ with $C \ne \infty$ and a compact set $\Omega \subseteq E^\times \times E^\times$ such that for every pair $d = (d_1, d_2)$ of units of $E$,
--   $$\int^{-}_{\xi \in E} \int^{-}_{k \in \mathbf{K}} \bigl\|\varphi\bigl(k^{-1} \cdot \begin{pmatrix} d_1 & 0 \\ 0 & d_2\end{pmatrix} \cdot \begin{pmatrix} 1 & \xi \\ 0 & 1\end{pmatrix} \cdot \sigma(k)\bigr)\bigr\|_{e}\, d\kappa(k)\, d\lambda(\xi) \;\le\; \mathbf{1}_\Omega(d)\, C,$$
--   where $\sigma$ acts on $\mathrm{GL}_2(E)$ entrywise through $\sigma \otimes \mathrm{id}$ on $E$, the integrals are lower Lebesgue integrals of the extended-norm integrand, and the right-hand side is $C$ for $d \in \Omega$ and $0$ otherwise; in particular the double integral vanishes for $d \notin \Omega$.
--
--   This is the archimedean "window" estimate for twisted orbital integrals on $\mathrm{GL}_2$ over $L \otimes_K \mathbb{A}_{K,\infty}$: compact support of the test function confines the diagonal parameter $d$ to a compact subset of $E^\times \times E^\times$ and bounds the $\kappa$-by-$\lambda$ integral uniformly in $d$. It feeds the comparison of twisted orbital integrals used in the archimedean component of the cubic-induction argument, being cited by [`AutomorphicForm.exists_forall_prod_infinitePlace_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegralOn_tensorArch_scalar_mul`](thm.html#AutomorphicForm.exists_forall_prod_infinitePlace_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegralOn_tensorArch_scalar_mul); compactness of the maximal compact subgroup entering the statement comes from [`NumberField.InfiniteAdeleRing.exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup`](thm.html#NumberField.InfiniteAdeleRing.exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_forall_lintegral_lintegral_enorm_diagUnits2_unipotentGL2_sigmaGL_le_indicator.lean

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

theorem AutomorphicForm.exists_isCompact_forall_lintegral_lintegral_enorm_diagUnits2_unipotentGL2_sigmaGL_le_indicator
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (κ : @Measure (↥(((⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent L w) :
          Subgroup (GL (Fin 2) (InfiniteAdeleRing L))).comap (AutomorphicForm.archIdentGL K L) :
        Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))))) (borel _))
    (hκ : @Measure.IsHaarMeasure _ _ _ (borel _) κ)
    (φ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ) (hφs : HasCompactSupport φ) (hφb : ∃ M : ℝ, ∀ g, ‖φ g‖ ≤ M) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ Ω : Set ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ), IsCompact Ω ∧
      ∀ d : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
        ∫⁻ ξ : (L ⊗[K] InfiniteAdeleRing K), @lintegral _ (borel _) κ (fun k =>
            ‖φ ((k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ * diagUnits2 d.1 d.2 * AutomorphicForm.unipotentGL2 ξ *
                AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))‖ₑ) ∂lam ≤
          Ω.indicator (fun _ => C) d := by sorry
