-- Prove2me | Theorems.Thm_Arxiv2108_02600_flat_surface_plane_waves
-- name    : Arxiv2108_02600.flat_surface_plane_waves
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T10:14:31.283124+00:00
-- url     : https://prove2.me/theorems/dcfbb5d7-4263-4dee-b97b-1d32200db8fe
-- title:
--   Example 1, eq. (5.3): exact scattered fields for the flat surface
-- statement:
--   Take the flat surface $f=0$ and the incident direction $\theta=(0,-1)$. The plane waves $u^{\rm inc}_p=\theta e^{i\kappa_px\cdot\theta}$ and $u^{\rm inc}_s=\theta^\perp e^{i\kappa_sx\cdot\theta}$, $\theta^\perp=(\theta_2,-\theta_1)$, are
--
--   $$u^{\rm inc}_1(x)=(0,-e^{-i\kappa_px_2}),\qquad u^{\rm inc}_2(x)=(-e^{-i\kappa_sx_2},0).$$
--
--   The solutions of (DP) with data $g=-u^{\rm inc}_1$ and $g=-u^{\rm inc}_2$ on $x_2=0$ are, respectively,
--
--   $$u^{\rm sc}_1(x)=(0,e^{i\kappa_px_2}),\qquad u^{\rm sc}_2(x)=(e^{i\kappa_sx_2},0)\qquad(5.3).$$
--
--   Each solves (DP), and any solution of (DP) with the same data agrees with it in $\Omega=\{x_2>0\}$.
--
--   **Formalization Note** "The scattered field" is stated as: the field solves (DP), and every solution of (DP) with the same data coincides with it on $\Omega$. The paper says the formulas are "easily seen". It does not check the radiation condition (2.3).
-- source:
--   J. Li, X. Liu, B. Zhang and H. Zhang, The Nyström method for elastic wave scattering by unbounded rough surfaces, arXiv:2108.02600v1 (2021), claim c013; Section 5, Example 1, incident fields before (5.3) and eq. (5.3), PDF pp. 17-18

import Mathlib
import Definitions.Def_Arxiv2108_02600_Basic

open MeasureTheory Filter Topology

namespace Arxiv2108_02600

theorem flat_surface_plane_waves (P : Lame) :
    let f0 : ℝ → ℝ := fun _ => 0
    let θ : Fin 2 → ℝ := ![0, -1]
    let u1 : Pt → Fin 2 → ℂ := fun x => ![0, Complex.exp (Complex.I * (P.kp : ℂ) * (x 1 : ℂ))]
    let u2 : Pt → Fin 2 → ℂ := fun x => ![Complex.exp (Complex.I * (P.ks : ℂ) * (x 1 : ℂ)), 0]
    (∀ x : Pt, planeWaveP P θ x = ![0, -Complex.exp (-(Complex.I * (P.kp : ℂ) * (x 1 : ℂ)))] ∧
      planeWaveS P θ x = ![-Complex.exp (-(Complex.I * (P.ks : ℂ) * (x 1 : ℂ))), 0]) ∧
    (IsDPSolution P f0 (fun x => -planeWaveP P θ x) u1 ∧
      ∀ v : Pt → Fin 2 → ℂ, IsDPSolution P f0 (fun x => -planeWaveP P θ x) v →
        ∀ x ∈ domainAbove f0, v x = u1 x) ∧
    (IsDPSolution P f0 (fun x => -planeWaveS P θ x) u2 ∧
      ∀ v : Pt → Fin 2 → ℂ, IsDPSolution P f0 (fun x => -planeWaveS P θ x) v →
        ∀ x ∈ domainAbove f0, v x = u2 x) := by sorry

end Arxiv2108_02600
