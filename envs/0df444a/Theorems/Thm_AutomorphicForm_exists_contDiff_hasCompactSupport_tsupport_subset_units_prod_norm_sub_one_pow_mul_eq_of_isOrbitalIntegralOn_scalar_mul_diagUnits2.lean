-- Prove2me | Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_scalar_mul_diagUnits2
-- name    : AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_scalar_mul_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/419b1f28-c7fe-5868-b1d6-f6589a071ed5
-- title:
--   Smooth archimedean window for normalised split orbital integrals
-- statement:
--   Let $K$ be a number field and $K_\infty$ its infinite adele ring. Let $fa : \mathrm{GL}_2(K_\infty)\to\mathbb C$ be an archimedean test factor, i.e. $fa$ has compact support and there is a map $\Psi$ on $2\times 2$ matrices over the mixed space $\mathbb R^{r_1}\times\mathbb C^{r_2}$ of $K$, smooth of class $C^\infty$ over $\mathbb R$, with $fa(g)=\Psi$ applied to the entries of $g$ transported by the ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace`. Let $\nu$ be a Haar measure on $\mathrm{GL}_2(K_\infty)$ for its Borel $\sigma$-algebra and $\rho$ a Haar measure on $K_\infty^\times$, the latter carrying a Borel measurable structure. Then there exists $\Phi : (\mathrm{Fin}\,2\to\mathbb R^{r_1}\times\mathbb C^{r_2})\to\mathbb C$, smooth of class $C^\infty$ over $\mathbb R$ and with compact support, such that: (i) if $\Phi(p)\neq 0$ then both components $p_0,p_1$ pull back under `InfiniteAdeleRing.ringEquiv_mixedSpace` to units of $K_\infty$; (ii) there is a compact set $Ca\subseteq K_\infty^\times\times K_\infty^\times$ with every point of the topological support of $\Phi$ of the form $(\iota(q_1),\iota(q_2))$ for some $(q_1,q_2)\in Ca$, where $\iota$ denotes the above isomorphism; and (iii) for all $u,z\in K_\infty^\times$ with $u_w\neq 1$ at every infinite place $w$, writing $\gamma = z\cdot\mathrm{diag}(u,1)$ (the scalar matrix of $z$ times `diagUnits2 u 1`), for every measure $\tau$ on the centraliser of $\{\gamma\}$ in $\mathrm{GL}_2(K_\infty)$ with its Borel $\sigma$-algebra such that $\int g\,d\tau = \int g(\mathrm{diag}(a,b))\,d(\rho\times\rho)(a,b)$ for every $g : \mathrm{GL}_2(K_\infty)\to\mathbb C$, and every $I\in\mathbb C$ which is an orbital integral of $fa$ at $\gamma$ with respect to $\nu$ and $\tau$ — meaning there is a weight $w_0 : \mathrm{GL}_2(K_\infty)\to\mathbb R$, non-negative, measurable, of compact support, with $\int_{\text{centraliser}} w_0(tx)\,d\tau = 1$ whenever $fa(x^{-1}\gamma x)\neq 0$, and $I = \int fa(x^{-1}\gamma x)\,w_0(x)\,d\nu(x)$ — one has $$\Big(\prod_{w\mid\infty}\|u_w-1\|^{\,m_w}\Big)\cdot I = \Phi(\iota(u),\iota(z)),$$ with $m_w$ the multiplicity of the infinite place $w$.
--
--   This is the archimedean Harish-Chandra descent for split regular classes in $\mathrm{GL}_2$, packaged so that the normalised orbital integral at $z\cdot\mathrm{diag}(u,1)$, for all admissible choices of section weight and for one fixed normalisation of the torus measure, is the value of a single compactly supported smooth function of the pair $(u,z)$ in the mixed space, whose support sits inside a compact set of pairs of units. It is used by the variants of the statement for the archimedean component of adelic $\mathrm{GL}_2$ with a central scalar, and thence in the comparison of geometric terms of the trace formula.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_scalar_mul_diagUnits2.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

attribute [local instance] AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in

theorem AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_scalar_mul_diagUnits2
    (K : Type) [Field K] [NumberField K]
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : AutomorphicForm.IsArchTestFactor K fa)
    (ν : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hν : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) ν)
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
    (ρ : Measure (InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure] :
    ∃ Φ : (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧
      (∀ p : Fin 2 → mixedEmbedding.mixedSpace K, Φ p ≠ 0 →
        IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)) ∧
          IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1))) ∧
      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport Φ, ∃ q ∈ Ca,
          p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) ∧
      ∀ (u z : (InfiniteAdeleRing K)ˣ), (∀ w : InfinitePlace K, (u : InfiniteAdeleRing K) w ≠ 1) →
        ∀ (τ : Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1} : Set (GL (Fin 2) (InfiniteAdeleRing K))))),
          (∀ g : GL (Fin 2) (InfiniteAdeleRing K) → ℂ,
              ∫ t, g (t : GL (Fin 2) (InfiniteAdeleRing K)) ∂τ =
                ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, g (diagUnits2 p.1 p.2) ∂(ρ.prod ρ)) →
          ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) ν
              (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) τ fa I →
            ((∏ w : InfinitePlace K, ‖(u : InfiniteAdeleRing K) w - 1‖ ^ w.mult : ℝ) : ℂ) * I =
              Φ ![InfiniteAdeleRing.ringEquiv_mixedSpace K (u : InfiniteAdeleRing K),
                InfiniteAdeleRing.ringEquiv_mixedSpace K (z : InfiniteAdeleRing K)] := by sorry
