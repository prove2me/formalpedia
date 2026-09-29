-- Prove2me | Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_pow_mul_integral_integral_unipotentGL2_eq_of_isArchTestFactor
-- name    : AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_pow_mul_integral_integral_unipotentGL2_eq_of_isArchTestFactor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/9c639679-f60c-568a-bbf1-4e504f1152a0
-- title:
--   Smooth archimedean window for unipotent orbital integrals
-- statement:
--   Let $K$ be a number field, equip the infinite adele ring $K_\infty = \mathrm{InfiniteAdeleRing}\,K$ with its Borel $\sigma$-algebra, let $\lambda$ be an additive Haar measure on $K_\infty$, and let $\kappa$ be a Haar measure, for the Borel $\sigma$-algebra, on the subgroup $\mathbf K_\infty \le GL_2(K_\infty)$ obtained as the infimum over the infinite places $w$ of the pullbacks along $\mathrm{archComponent}\,K\,w$ (entrywise evaluation at $w$) of the subgroup of row isometries of $GL_2(K_w)$, that is of those $k$ with $\|\det k\| = 1$ and $\|xk_{00}+yk_{10}\|^2 + \|xk_{01}+yk_{11}\|^2 = \|x\|^2 + \|y\|^2$ for all $x,y \in K_w$. Let $f_a : GL_2(K_\infty) \to \mathbb C$ be an archimedean test factor: $f_a$ has compact support and there is a $C^\infty$ function on $2\times 2$ matrices over the mixed space $\mathbb R^{r_1}\times\mathbb C^{r_2}$ of $K$ with $f_a(g)$ its value at the matrix of entries of $g$ read in the mixed space via `InfiniteAdeleRing.ringEquiv_mixedSpace`. Then there is $\Phi$ on pairs of elements of the mixed space, real $C^\infty$ and of compact support, such that $\Phi(p)\neq 0$ forces both $p_0$ and $p_1$ to come from units of $K_\infty$, such that for some compact set $C_a$ of pairs of units of $K_\infty$ every point of $\operatorname{tsupport}\Phi$ is the image $![\iota(q_1),\iota(q_2)]$ of some $q \in C_a$, and such that for all units $u, z$ of $K_\infty$,
--   $$\Big(\prod_{w\mid\infty}\|u_w\|^{\mathrm{mult}(w)}\Big)\int_{K_\infty}\int_{\mathbf K_\infty} f_a\big(k^{-1}\,(zI)\,\mathrm{diag}(u,1)\,\begin{pmatrix}1&x\\0&1\end{pmatrix}\,k\big)\,d\kappa(k)\,d\lambda(x) = \Phi\big(\iota(u),\iota(z)\big),$$
--   where $\iota$ denotes the mixed-space coordinates.
--
--   This is the archimedean window of the unipotent (constant) term: the double integral of an archimedean test factor over the maximal compact subgroup of $GL_2(K_\infty)$ and over the unipotent variable, multiplied by the normalising factor $\prod_w\|u_w\|^{\mathrm{mult}(w)}$, is realised as a smooth compactly supported function of $(u,z)$ in the mixed space whose support is carried by a compact set of pairs of units. It feeds the orbital-integral statement for scalar times $\mathrm{diag}(u,1)$, where the resulting $\Phi$ is used as a test function in the archimedean place of the trace comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_pow_mul_integral_integral_unipotentGL2_eq_of_isArchTestFactor.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped ENNReal

attribute [local instance] AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in

theorem AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_pow_mul_integral_integral_unipotentGL2_eq_of_isArchTestFactor
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    (lam : Measure (InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (κ : @Measure (↥(⨅ w : InfinitePlace K,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent K w) :
          Subgroup (GL (Fin 2) (InfiniteAdeleRing K)))) (borel _))
    (hκ : @Measure.IsHaarMeasure _ _ _ (borel _) κ)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : AutomorphicForm.IsArchTestFactor K fa) :
    ∃ Φ : (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧
      (∀ p : Fin 2 → mixedEmbedding.mixedSpace K, Φ p ≠ 0 →
        IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)) ∧
          IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1))) ∧
      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport Φ, ∃ q ∈ Ca,
          p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) ∧
      ∀ (u z : (InfiniteAdeleRing K)ˣ),
        ((∏ w : InfinitePlace K, ‖(u : InfiniteAdeleRing K) w‖ ^ w.mult : ℝ) : ℂ) *
            ∫ x, @integral _ ℂ _ _ (borel _) κ (fun k =>
                fa ((k : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ *
                  (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 * AutomorphicForm.unipotentGL2 x) *
                  (k : GL (Fin 2) (InfiniteAdeleRing K)))) ∂lam =
          Φ ![InfiniteAdeleRing.ringEquiv_mixedSpace K (u : InfiniteAdeleRing K),
              InfiniteAdeleRing.ringEquiv_mixedSpace K (z : InfiniteAdeleRing K)] := by sorry
