-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_forall_prod_norm_sub_one_pow_mul_eq_and_weighted_eq_mul_prod_norm_pow_mul_integral_integral_of_scalar_mul_diagUnits2
-- name    : AutomorphicForm.exists_pos_forall_prod_norm_sub_one_pow_mul_eq_and_weighted_eq_mul_prod_norm_pow_mul_integral_integral_of_scalar_mul_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/8ced40c2-2b3b-5bae-bd02-51666fa027b6
-- title:
--   Weighted archimedean Harish–Chandra descent at the split torus
-- statement:
--   Let $K$ be a number field and let $K_\infty$ denote its infinite adele ring. Fix a Haar measure $\nu$ on $GL_2(K_\infty)$ (for the Borel $\sigma$-algebra), an additive Haar measure $\lambda$ on $K_\infty$, a Haar measure $\rho$ on $K_\infty^{\times}$, and a Haar measure $\kappa$ on the subgroup $\mathbf{K}_\infty \le GL_2(K_\infty)$ cut out as the intersection, over the infinite places $w$, of the preimages under the component map $GL_2(K_\infty)\to GL_2(K_w)$ of the subgroup of those $k$ with $\|\det k\|=1$ satisfying $\|xk_{00}+yk_{10}\|^2+\|xk_{01}+yk_{11}\|^2=\|x\|^2+\|y\|^2$ for all $x,y$. Then there is a real $c>0$ such that the following holds. Let $f_a:GL_2(K_\infty)\to\mathbb{C}$ be an archimedean test factor, i.e. $f_a(g)=\Phi$ evaluated at the matrix of archimedean entries of $g$ for some smooth $\Phi$ on the space of $2\times2$ matrices over the mixed space of $K$, with $f_a$ of compact support; let $\omega:K_\infty\to\mathbb{R}$ and $W:GL_2(K_\infty)\to\mathbb{R}$ be continuous with $W\big(u'\cdot\mathrm{diag}(t',1)\,n(y)\,k\big)=\omega(y)$ for all units $u',t'$, all $y\in K_\infty$ and all $k\in\mathbf{K}_\infty$, where $u'$ denotes the scalar matrix and $n(y)=\begin{pmatrix}1&y\\0&1\end{pmatrix}$; let $u,z\in K_\infty^{\times}$ with $u_w\ne 1$ at every infinite place $w$, and let $v\in K_\infty^{\times}$ satisfy $v=1-u^{-1}$. Put $\gamma=z\cdot\mathrm{diag}(u,1)$ and let $\tau$ be a measure on the centraliser of $\gamma$ such that $\int g\,d\tau=\int g(\mathrm{diag}(p_1,p_2))\,d(\rho\otimes\rho)(p)$ for every $g:GL_2(K_\infty)\to\mathbb{C}$. Then, writing $P_1=\prod_w\|u_w-1\|^{m_w}$ and $P_0=\prod_w\|u_w\|^{m_w}$ with $m_w$ the multiplicity of $w$: first, every $I$ which is an orbital integral of $f_a$ at $\gamma$ relative to $(\nu,\tau)$ — that is, $I=\int f_a(x^{-1}\gamma x)\,s(x)\,d\nu(x)$ for some non-negative measurable $s$ of compact support with $\int_{\,\mathrm{centraliser}} s(tx)\,d\tau(t)=1$ whenever $f_a(x^{-1}\gamma x)\ne0$ — satisfies $$P_1\,I=c\,P_0\int_{K_\infty}\Big(\int_{\mathbf{K}_\infty} f_a\big(k^{-1}\gamma\,n(x)\,k\big)\,d\kappa(k)\Big)d\lambda(x);$$ second, every $J$ which is a $W$-weighted orbital integral of $f_a$ at $\gamma$ relative to $(\nu,\tau)$, i.e. $J=\int f_a(x^{-1}\gamma x)\,W(x)\,s(x)\,d\nu(x)$ for such a section function $s$, satisfies the same identity with the inner double integral weighted by $\omega(v^{-1}x)$. Both identities hold with the one constant $c$, which is independent of $f_a$, $\omega$, $W$, $u$, $z$, $v$, $\tau$.
--
--   This is the archimedean Harish–Chandra descent at the split torus of $GL_2$: the orbital integral at a regular split element $z\,\mathrm{diag}(u,1)$, normalised by the Weyl discriminant factor $\prod_w\|u_w-1\|^{m_w}$, is expressed as an integral over the unipotent coordinate of the $\mathbf{K}_\infty$-average of the test factor, and the same expression, with the Iwasawa weight inserted as $\omega(v^{-1}x)$, computes the weighted orbital integral. The two identities are stated with a common constant so that a downstream comparison may subtract a multiple of the plain orbital integral from the weighted one with exact cancellation; the result feeds the archimedean contributions in the weighted trace-formula step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_forall_prod_norm_sub_one_pow_mul_eq_and_weighted_eq_mul_prod_norm_pow_mul_integral_integral_of_scalar_mul_diagUnits2.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
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

theorem AutomorphicForm.exists_pos_forall_prod_norm_sub_one_pow_mul_eq_and_weighted_eq_mul_prod_norm_pow_mul_integral_integral_of_scalar_mul_diagUnits2
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
      ∀ (ω : InfiniteAdeleRing K → ℝ), Continuous ω →
      ∀ (W : GL (Fin 2) (InfiniteAdeleRing K) → ℝ), Continuous W →
        (∀ (u' t' : (InfiniteAdeleRing K)ˣ) (y : InfiniteAdeleRing K) (k : GL (Fin 2) (InfiniteAdeleRing K)),
            k ∈ (⨅ w : InfinitePlace K,
              (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent K w) :
                Subgroup (GL (Fin 2) (InfiniteAdeleRing K))) →
            W (Matrix.GeneralLinearGroup.scalar (Fin 2) u' * diagUnits2 t' 1 * AutomorphicForm.unipotentGL2 y * k) = ω y) →
      ∀ (u z : (InfiniteAdeleRing K)ˣ), (∀ w : InfinitePlace K, (u : InfiniteAdeleRing K) w ≠ 1) →
      ∀ (v : (InfiniteAdeleRing K)ˣ), (v : InfiniteAdeleRing K) = 1 - ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) →
        ∀ (τ : Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1} : Set (GL (Fin 2) (InfiniteAdeleRing K))))),
          (∀ g : GL (Fin 2) (InfiniteAdeleRing K) → ℂ,
              ∫ t, g (t : GL (Fin 2) (InfiniteAdeleRing K)) ∂τ =
                ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, g (diagUnits2 p.1 p.2) ∂(ρ.prod ρ)) →
          (∀ I : ℂ, AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) ν
              (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) τ fa I →
            ((∏ w : InfinitePlace K, ‖(u : InfiniteAdeleRing K) w - 1‖ ^ w.mult : ℝ) : ℂ) * I =
              (c : ℂ) * ((∏ w : InfinitePlace K, ‖(u : InfiniteAdeleRing K) w‖ ^ w.mult : ℝ) : ℂ) *
                ∫ x, @integral _ ℂ _ _ (borel _) κ (fun k =>
                    fa ((k : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ *
                      (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 * AutomorphicForm.unipotentGL2 x) *
                      (k : GL (Fin 2) (InfiniteAdeleRing K)))) ∂lam) ∧
          (∀ J : ℂ, AutomorphicForm.IsWeightedOrbitalIntegralOn (InfiniteAdeleRing K) ν W
              (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) τ fa J →
            ((∏ w : InfinitePlace K, ‖(u : InfiniteAdeleRing K) w - 1‖ ^ w.mult : ℝ) : ℂ) * J =
              (c : ℂ) * ((∏ w : InfinitePlace K, ‖(u : InfiniteAdeleRing K) w‖ ^ w.mult : ℝ) : ℂ) *
                ∫ x, (@integral _ ℂ _ _ (borel _) κ (fun k =>
                    fa ((k : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ *
                      (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 * AutomorphicForm.unipotentGL2 x) *
                      (k : GL (Fin 2) (InfiniteAdeleRing K))))) *
                  ((ω (((v⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * x) : ℝ) : ℂ) ∂lam) := by sorry
