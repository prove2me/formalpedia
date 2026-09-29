-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_forall_integral_centralizer_diagUnits2_eq_integral_prod_of_map_eq
-- name    : AutomorphicForm.exists_isHaarMeasure_forall_integral_centralizer_diagUnits2_eq_integral_prod_of_map_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/05be96a3-172e-5bc3-95d0-ffc5d2bbd259
-- title:
--   Uniform Haar normalisation on split regular centralisers over K_∞
-- statement:
--   Let $K$ be a number field, and equip the infinite adele ring $K_\infty =$ `InfiniteAdeleRing K` and its unit group with measurable structures that are the Borel structures of their topologies; the centraliser subgroups occurring below carry the Borel $\sigma$-algebra of the subspace topology. Let $\tau_0$ be an arbitrary measure on $K_\infty \times K_\infty$. The assertion is that there exists a Haar measure $\rho$ on $K_\infty^\times$ with the following property: for all units $p, q \in K_\infty^\times$ such that the element $\mathrm{diag}(p,q) \in GL_2(K_\infty)$ (the invertible matrix $!![p,0;0,q]$, with inverse $!![p^{-1},0;0,q^{-1}]$) is regular semisimple in the sense that $\mathrm{tr}^2 - 4\det$ of its underlying matrix is a unit of $K_\infty$, and for every Haar measure $\tau$ on the centraliser of $\{\mathrm{diag}(p,q)\}$ in $GL_2(K_\infty)$ whose push-forward along the map sending $x$ to the pair of diagonal entries $(x_{00}, x_{11})$ of its underlying matrix equals $\tau_0$, one has, for every function $g : GL_2(K_\infty) \to \mathbb{C}$ whatsoever (no measurability or integrability is assumed), the equality $$\int_{Z(\mathrm{diag}(p,q))} g(x)\,d\tau(x) = \int_{K_\infty^\times \times K_\infty^\times} g(\mathrm{diag}(r_1,r_2))\,d(\rho \times \rho)(r).$$ Thus a single $\rho$, depending only on $\tau_0$, computes every $\tau_0$-normalised centraliser integral at a split regular element.
--
--   This is the normalisation step which converts the condition that a Haar measure on the centraliser of a regular split element pushes forward to a fixed measure $\tau_0$ on $K_\infty \times K_\infty$ into an integration formula over $K_\infty^\times \times K_\infty^\times$ against a product Haar measure, uniformly in the regular split class; it rests on the uniqueness of Haar measure up to scalar. It is used in the archimedean estimates for the weighted and twisted weighted orbital integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isHaarMeasure_forall_integral_centralizer_diagUnits2_eq_integral_prod_of_map_eq.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.exists_isHaarMeasure_forall_integral_centralizer_diagUnits2_eq_integral_prod_of_map_eq
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
    (τ₀ : Measure (InfiniteAdeleRing K × InfiniteAdeleRing K)) :
    ∃ ρ : Measure (InfiniteAdeleRing K)ˣ, ρ.IsHaarMeasure ∧
      ∀ (p q : (InfiniteAdeleRing K)ˣ), AutomorphicForm.IsRegularSemisimple (diagUnits2 p q) →
      ∀ (τ : Measure (Subgroup.centralizer ({diagUnits2 p q} : Set (GL (Fin 2) (InfiniteAdeleRing K))))),
        τ.IsHaarMeasure →
        Measure.map
            (fun x : Subgroup.centralizer ({diagUnits2 p q} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
              ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
                ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :
                InfiniteAdeleRing K × InfiniteAdeleRing K))
            τ = τ₀ →
      ∀ g : GL (Fin 2) (InfiniteAdeleRing K) → ℂ,
        ∫ x, g (x : GL (Fin 2) (InfiniteAdeleRing K)) ∂τ =
          ∫ r : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, g (diagUnits2 r.1 r.2) ∂(ρ.prod ρ) := by sorry
