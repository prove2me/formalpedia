-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Real_exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt
-- name    : AutomorphicForm.GL2Real.exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/782eeb75-3941-5e60-b63c-093577433e87
-- title:
--   Haar measure on an elliptic torus in polar form
-- statement:
--   Fix reals $r,\theta$ with $r>0$ and $\sin\theta\neq 0$, and let $\gamma=\mathrm{ellipticElt}\,r\,\theta$ be the element of $\mathrm{GL}_2(\mathbb{R})$ given by the matrix $\begin{pmatrix} r\cos\theta & r\sin\theta\\ -r\sin\theta & r\cos\theta\end{pmatrix}$ (invertible because its determinant is $r^2$). Consider the centralizer subgroup of $\{\gamma\}$ in $\mathrm{GL}_2(\mathbb{R})$, equipped with the Borel $\sigma$-algebra of its subspace topology (`centralizerBorel`), and let $\tau$ be a Haar measure on it. The assertion is that there exists $c\in\mathbb{R}_{\ge 0}$ with $c>0$ such that the pushforward of $\tau$ along the inclusion `Subtype.val` into $\mathrm{GL}_2(\mathbb{R})$, the latter carrying the Borel $\sigma$-algebra of its topology (`glBorelOf`), equals $c$ times the pushforward, along the map $(q_1,q_2)\mapsto \mathrm{ellipticElt}\,q_1\,q_2$ for $q_1>0$ (and $\mapsto 1$ otherwise), of the measure on $\mathbb{R}\times\mathbb{R}$ obtained from Lebesgue measure restricted to $(0,\infty)\times(0,2\pi)$ by multiplying by the density $q\mapsto \mathrm{ofReal}\,q_1^{-1}$. Thus, in polar coordinates $(\rho,\varphi)$ on the non-split torus, Haar measure is a positive multiple of $\rho^{-1}\,d\rho\,d\varphi$.
--
--   This identifies, up to a positive constant, Haar measure on the non-split (elliptic) maximal torus of $\mathrm{GL}_2(\mathbb{R})$ attached to a regular elliptic element with the explicit polar-coordinate measure $d\rho\,d\varphi/\rho$. It is used to evaluate orbital integrals at elliptic elements, being cited by [`AutomorphicForm.GL2Real.orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div`](thm.html#AutomorphicForm.GL2Real.orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div) and its twisted counterpart [`AutomorphicForm.GL2Twisted.twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div`](thm.html#AutomorphicForm.GL2Twisted.twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Real_exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt.lean

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MeasureTheory
open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt (r θ : ℝ) (hr : 0 < r)
    (hθ : Real.sin θ ≠ 0)
    (τ : @Measure (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)))
      (centralizerBorel ℝ (ellipticElt r θ hr)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (ellipticElt r θ hr)) τ) :
    ∃ c : NNReal, 0 < c ∧
      @Measure.map _ _ (centralizerBorel ℝ (ellipticElt r θ hr)) (glBorelOf ℝ) Subtype.val τ =
        c • @Measure.map (ℝ × ℝ) _ _ (glBorelOf ℝ)
          (fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
          ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
            (fun q => ENNReal.ofReal q.1⁻¹)) := by sorry
