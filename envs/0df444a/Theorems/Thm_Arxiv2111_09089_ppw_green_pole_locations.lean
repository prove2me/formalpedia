-- Prove2me | Theorems.Thm_Arxiv2111_09089_ppw_green_pole_locations
-- name    : Arxiv2111_09089.ppw_green_pole_locations
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T10:41:58.891434+00:00
-- url     : https://prove2.me/theorems/c29cafe1-0258-53c5-b4e0-cfa833db76c0
-- title:
--   Eqs. (9)-(10): the parallel-plate spectral Green's function has only poles (as corrected)
-- statement:
--   Let $k_0>0$ and $d>0$, let $\epsilon_{r1}\ne0$, and let the source and observer positions satisfy $0\le z,z'\le d$. Let $g(\xi)=g(\xi;z,z')$ be the spectral Green's function of eq. (9) of the parallel-plate waveguide, with $k_z=k_0\sqrt{\epsilon_{r1}-\xi^2}$. Then:
--
--   1. $g$ is meromorphic on the whole complex $\xi$ plane. In particular it has no branch points, although its formula contains $\sqrt{\epsilon_{r1}-\xi^2}$.
--   2. $g$ is holomorphic at every $\xi$ outside the set
--   $$\Big\{\xi:\ \xi^2=\epsilon_{r1}-\Big(\frac{n\pi}{k_0d}\Big)^2,\ n=0,1,2,\dots\Big\}.$$
--   So every singularity of $g$ is a pole, and it lies among the points $\xi_{p,n}=\pm\sqrt{\epsilon_{r1}-(n\pi/(k_0d))^2}$. Not every such point need be a singularity.
--
--   **Formalization Note** Eq. (10) prints $\xi_{p,n}=\sqrt{1-\frac1{\epsilon_{r1}}\big(\frac{n\pi}{k_0d}\big)^2}$, which is $\sqrt{\epsilon_{r1}-(n\pi/(k_0d))^2}$ divided by $\sqrt{\epsilon_{r1}}$. With $\xi$ normalised to the vacuum wavenumber as in eq. (1), the zeros of $1-e^{-2jk_zd}$ are at $\xi^2=\epsilon_{r1}-(n\pi/(k_0d))^2$. For $\epsilon_{r1}=1-0.05j$, $d=5\lambda_0$, $n=1$, the printed point is not a singularity of $g$. The corrected set is stated, with both signs of the root. "Located at" is read as inclusion: for some $n$ (including $n=0$, and $n$ with $\sin(n\pi z/d)\sin(n\pi z'/d)=0$) the singularity is removable.
-- source:
--   Y. Hadad, On the use of the Padé-Fourier approximation in fast evaluation of the Green's function of layered media, arXiv:2111.09089v1 (2021), claim c007; Section III-A-1, eqs. (9)-(10), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv2111_09089_Basic

open Complex MeasureTheory Filter Topology Asymptotics

namespace Arxiv2111_09089

theorem ppw_green_pole_locations (k0 d : ℝ) (hk0 : 0 < k0) (hd : 0 < d) (ε : ℂ) (hε : ε ≠ 0)
    (z z' : ℝ) (hz : z ∈ Set.Icc 0 d) (hz' : z' ∈ Set.Icc 0 d) :
    MeromorphicOn (ppwGreen k0 d ε z z') Set.univ ∧
    ∀ ξ : ℂ, (∀ n : ℕ, ξ ^ 2 ≠ ε - ((n * Real.pi / (k0 * d) : ℝ) : ℂ) ^ 2) →
      AnalyticAt ℂ (ppwGreen k0 d ε z z') ξ := by sorry

end Arxiv2111_09089
