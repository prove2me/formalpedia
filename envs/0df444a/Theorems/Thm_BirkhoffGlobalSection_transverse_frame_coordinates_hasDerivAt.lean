-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_transverse_frame_coordinates_hasDerivAt
-- name    : BirkhoffGlobalSection.transverse_frame_coordinates_hasDerivAt
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T01:04:56.594049+00:00
-- url     : https://prove2.me/theorems/179d0f42-a0ae-4421-a5b5-de82cebfaef9
-- title:
--   Transverse frame equation along a Hamiltonian orbit
-- statement:
--   The transverse frame equation along a Hamiltonian orbit in $\mathbb{R}^4$.
--
--   Let $g(t)$ be the gradient of a Hamiltonian along an orbit, so that $g'=H\,(Ig)$, where $H$ is the symmetric Hessian at time $t$ and $I,J,K$ are the quaternionic matrices of the definitions. Let $w(t)$ solve the variational equation $w'=I H w$. Suppose $w$ is tangent to the level set ($w\cdot g=0$) and $g\neq 0$. Then the frame coordinates $z=(w\cdot Jg,\;w\cdot Kg)$ satisfy
--   $$|g|^2\,z'=\begin{pmatrix}0&-1\\1&0\end{pmatrix}\begin{pmatrix}c+s_{11}&s_{12}\\ s_{12}&c+s_{22}\end{pmatrix}z+(g\cdot H Ig)\,z,$$
--   where $c=H(Ig,Ig)$ and $s_{11}=H(Jg,Jg)$, $s_{12}=H(Jg,Kg)$, $s_{22}=H(Kg,Kg)$.
--
--   The component of $w$ along the flow direction $Ig$ cancels exactly. As a consequence, the polar angle of $z$ has derivative $|g|^{-2}\langle S e_\theta,e_\theta\rangle$ with $S=cI+\hat H$. In particular it is strictly increasing wherever the tangential Hessian is positive definite.
-- source:
--   Hofer-Wysocki-Zehnder, The dynamics on three-dimensional strictly convex energy surfaces (1998), Section 3; direct computation

import Mathlib
import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity

namespace BirkhoffGlobalSection

open Matrix TangentialHessian

/-- The transverse frame equation. Let `g(t)` be the gradient along a Hamiltonian orbit, so
`g' = H (I g)`, and let `w(t)` solve the variational equation `w' = I H w`, where `H` is the
symmetric Hessian at time `t`. If `w` is tangent to the level set (`w·g = 0`) and `g ≠ 0`, then
the frame coordinates `z = (w·Jg, w·Kg)` satisfy
`|g|² z' = J₂ [[c + s₁₁, s₁₂], [s₁₂, c + s₂₂]] z + (g·H Ig) z`,
with `c = H(Ig, Ig)` and `sᵢⱼ` the entries of `H` on `(Jg, Kg)`. -/
theorem transverse_frame_coordinates_hasDerivAt (g w : ℝ → Phase)
    (H : Matrix (Fin 4) (Fin 4) ℝ) (t : ℝ) (hH : H.IsSymm)
    (hg : HasDerivAt g (H *ᵥ (qI *ᵥ g t)) t)
    (hw : HasDerivAt w (qI *ᵥ (H *ᵥ w t)) t)
    (htan : w t ⬝ᵥ g t = 0) (hg0 : g t ≠ 0) :
    HasDerivAt (fun s => transverseFrameCoordinates (g s) (w s))
      ((g t ⬝ᵥ g t)⁻¹ •
        ![-((qJ *ᵥ g t) ⬝ᵥ (H *ᵥ (qK *ᵥ g t)) * (w t ⬝ᵥ (qJ *ᵥ g t))
              + (qK *ᵥ g t) ⬝ᵥ (H *ᵥ (qK *ᵥ g t)) * (w t ⬝ᵥ (qK *ᵥ g t)))
            - (qI *ᵥ g t) ⬝ᵥ (H *ᵥ (qI *ᵥ g t)) * (w t ⬝ᵥ (qK *ᵥ g t))
            + g t ⬝ᵥ (H *ᵥ (qI *ᵥ g t)) * (w t ⬝ᵥ (qJ *ᵥ g t)),
          (qJ *ᵥ g t) ⬝ᵥ (H *ᵥ (qJ *ᵥ g t)) * (w t ⬝ᵥ (qJ *ᵥ g t))
              + (qJ *ᵥ g t) ⬝ᵥ (H *ᵥ (qK *ᵥ g t)) * (w t ⬝ᵥ (qK *ᵥ g t))
            + (qI *ᵥ g t) ⬝ᵥ (H *ᵥ (qI *ᵥ g t)) * (w t ⬝ᵥ (qJ *ᵥ g t))
            + g t ⬝ᵥ (H *ᵥ (qI *ᵥ g t)) * (w t ⬝ᵥ (qK *ᵥ g t))]) t := by
  sorry

end BirkhoffGlobalSection
