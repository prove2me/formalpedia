-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_forall_prod_norm_sub_one_pow_mul_eq_mul_prod_norm_pow_mul_integral_integral_of_isOrbitalIntegralOn_scalar_mul_diagUnits2
-- name    : AutomorphicForm.exists_pos_forall_prod_norm_sub_one_pow_mul_eq_mul_prod_norm_pow_mul_integral_integral_of_isOrbitalIntegralOn_scalar_mul_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/adcd3c23-b9b5-5b15-bb8f-11699eb271ae
-- title:
--   Archimedean descent of split orbital integrals to the torus
-- statement:
--   Let $K$ be a number field and $K_\infty$ its infinite adele ring. Fix a Haar measure $\nu$ on $GL_2(K_\infty)$ (for the Borel $\sigma$-algebra), an additive Haar measure $\lambda$ on $K_\infty$, a Haar measure $\rho$ on $K_\infty^\times$, and a Haar measure $\kappa$ on the subgroup $\mathbf{K} = \bigcap_{w\mid\infty}$ of those $k\in GL_2(K_\infty)$ whose image in $GL_2(K_w)$ satisfies $\|\det k\|=1$ and $\|xk_{00}+yk_{10}\|^2+\|xk_{01}+yk_{11}\|^2=\|x\|^2+\|y\|^2$ for all $x,y$, together with the usual Borel measurability assumptions. Then there is a real $c>0$, depending on none of the data below, such that the following holds for every $f_a : GL_2(K_\infty)\to\mathbb{C}$ that has compact support and is of the form $g\mapsto \Phi$ of the matrix of archimedean entries of $g$ for some $C^\infty$ function $\Phi$ on $2\times 2$ matrices over the mixed space of $K$; for all units $u,z$ of $K_\infty$ with $u_w\neq 1$ at every infinite place $w$; for every measure $\tau$ on the centraliser of $\gamma = z\cdot\mathrm{diag}(u,1)$ in $GL_2(K_\infty)$ such that $\int g\,d\tau = \int g(\mathrm{diag}(a,b))\,d(\rho\otimes\rho)(a,b)$ for every function $g$ on $GL_2(K_\infty)$ whatsoever; and for every $I\in\mathbb{C}$ which is an orbital integral of $f_a$ at $\gamma$ relative to $(\nu,\tau)$, i.e. for which there is a non-negative measurable compactly supported $w$ on $GL_2(K_\infty)$ with $\int_{\tau} w(tx)\,d\tau(t)=1$ whenever $f_a(x^{-1}\gamma x)\neq 0$ and $I=\int f_a(x^{-1}\gamma x)\,w(x)\,d\nu(x)$: one has $$\Big(\prod_{w}\|u_w-1\|^{m_w}\Big)\, I = c\,\Big(\prod_{w}\|u_w\|^{m_w}\Big)\int_{K_\infty}\int_{\mathbf{K}} f_a\big(k^{-1}\,\gamma\,n(x)\,k\big)\,d\kappa(k)\,d\lambda(x),$$ where $m_w$ is the multiplicity of the infinite place $w$ and $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$.
--
--   This is the archimedean case of Harish-Chandra descent for a regular split element of $GL_2$: the orbital integral at $z\cdot\mathrm{diag}(u,1)$, weighted by $\prod_w\|u_w-1\|^{m_w}$, is expressed as a constant multiple of an integral over the unipotent radical and the maximal compact subgroup, with the Weyl-type factor $\prod_w\|u_w\|^{m_w}$. It rests on the Iwasawa integration formula on $GL_2(K_\infty)$, the Iwasawa decomposition together with compactness of the archimedean row-isometry group, and the computation of the module of a unit of $K_\infty$ as $\prod_w\|a_w\|^{m_w}$; it is used to produce a smooth compactly supported function of the torus parameter whose values are the weighted orbital integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_forall_prod_norm_sub_one_pow_mul_eq_mul_prod_norm_pow_mul_integral_integral_of_isOrbitalIntegralOn_scalar_mul_diagUnits2.lean

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

theorem AutomorphicForm.exists_pos_forall_prod_norm_sub_one_pow_mul_eq_mul_prod_norm_pow_mul_integral_integral_of_isOrbitalIntegralOn_scalar_mul_diagUnits2
    (K : Type) [Field K] [NumberField K]
    (ν : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hν : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) ν)
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    (lam : Measure (InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
    (ρ : Measure (InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure]
    (κ : @Measure (↥(⨅ w : InfinitePlace K,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent K w) :
          Subgroup (GL (Fin 2) (InfiniteAdeleRing K)))) (borel _))
    (hκ : @Measure.IsHaarMeasure _ _ _ (borel _) κ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ), AutomorphicForm.IsArchTestFactor K fa →
      ∀ (u z : (InfiniteAdeleRing K)ˣ), (∀ w : InfinitePlace K, (u : InfiniteAdeleRing K) w ≠ 1) →
        ∀ (τ : Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1} : Set (GL (Fin 2) (InfiniteAdeleRing K))))),
          (∀ g : GL (Fin 2) (InfiniteAdeleRing K) → ℂ,
              ∫ t, g (t : GL (Fin 2) (InfiniteAdeleRing K)) ∂τ =
                ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, g (diagUnits2 p.1 p.2) ∂(ρ.prod ρ)) →
          ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) ν
              (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) τ fa I →
            ((∏ w : InfinitePlace K, ‖(u : InfiniteAdeleRing K) w - 1‖ ^ w.mult : ℝ) : ℂ) * I =
              (c : ℂ) * ((∏ w : InfinitePlace K, ‖(u : InfiniteAdeleRing K) w‖ ^ w.mult : ℝ) : ℂ) *
                ∫ x, @integral _ ℂ _ _ (borel _) κ (fun k =>
                    fa ((k : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ *
                      (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 * AutomorphicForm.unipotentGL2 x) *
                      (k : GL (Fin 2) (InfiniteAdeleRing K)))) ∂lam := by sorry
