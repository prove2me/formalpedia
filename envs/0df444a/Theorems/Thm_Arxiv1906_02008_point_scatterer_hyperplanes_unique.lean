-- Prove2me | Theorems.Thm_Arxiv1906_02008_point_scatterer_hyperplanes_unique
-- name    : Arxiv1906_02008.point_scatterer_hyperplanes_unique
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T14:40:42.855863+00:00
-- url     : https://prove2.me/theorems/45908427-451b-4956-9475-cd543190f200
-- title:
--   Theorem 3.1: single-pair multi-frequency data determine the hyperplanes through point-like scatterers (nonvanishing combined strengths)
-- statement:
--   Let $n\in\{2,3\}$, $0<k_-<k^+$, and let $\hat x,\theta\in\mathbb{S}^{n-1}$ with $\hat x\ne\theta$. Consider two configurations of point-like scatterers, $(z_m,\tau_m)_{m=1}^M$ and $(z'_m,\tau'_m)_{m=1}^{M'}$, with $z_m,z'_m\in\mathbb{R}^n$ and $\tau_m,\tau'_m\in\mathbb{C}$, and assume that in each configuration the scatterers lying on a common hyperplane $\Pi_{\alpha}$ have nonzero total strength: for every $m$,
--   $$\sum_{m':\ z_{m'}\cdot(\theta-\hat x)=z_m\cdot(\theta-\hat x)}\tau_{m'}\ne0,$$
--   and likewise for $(z',\tau')$. If the model far fields $\tilde u^\infty(\hat x,\theta,k)=\sum_m\tau_me^{ikz_m\cdot(\theta-\hat x)}$ of the two configurations agree for all $k\in(k_-,k^+)$, then the two families of hyperplanes $\{\Pi_{\alpha_m}:1\le m\le M\}$ and $\{\Pi_{\alpha'_m}:1\le m\le M'\}$ coincide, where $\alpha_m=-z_m\cdot(\theta-\hat x)$ and $\Pi_\alpha=\{y:\ y\cdot(\theta-\hat x)+\alpha=0\}$.
--
--   **Formalization Note** "Uniquely determined by the data" is stated as: two configurations with the same data on $(k_-,k^+)$ have the same set of hyperplanes. The nonvanishing-combined-strength hypothesis is not in the paper; without it the theorem is false (two scatterers on one hyperplane with $\tau_1=-\tau_2$ produce zero data wherever that hyperplane is). The number of scatterers may differ between the two configurations.
-- source:
--   Xia Ji and Xiaodong Liu, Inverse acoustic scattering problems with multi-frequency sparse backscattering far field data, arXiv:1906.02008v2 (2019), claim c018; Section 3, Theorem 3.1, eqs. (3.10)-(3.12), PDF p. 5

import Mathlib
import Definitions.Def_Arxiv1906_02008_Basic

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Arxiv1906_02008

theorem point_scatterer_hyperplanes_unique {n : ℕ} (hn : n = 2 ∨ n = 3)
    (km kp : ℝ) (hkm : 0 < km) (hk : km < kp)
    (xh θ : Rn n) (hxh : ‖xh‖ = 1) (hθ : ‖θ‖ = 1) (hne : xh ≠ θ)
    (M M' : ℕ) (z : Fin M → Rn n) (τ : Fin M → ℂ) (z' : Fin M' → Rn n) (τ' : Fin M' → ℂ)
    (hτ : ∀ m, (∑ m' ∈ Finset.univ.filter (fun m' => ⟪z m', θ - xh⟫ = ⟪z m, θ - xh⟫), τ m') ≠ 0)
    (hτ' : ∀ m, (∑ m' ∈ Finset.univ.filter (fun m' => ⟪z' m', θ - xh⟫ = ⟪z' m, θ - xh⟫), τ' m') ≠ 0)
    (hdata : ∀ k ∈ Ioo km kp, pointFarField z τ xh θ k = pointFarField z' τ' xh θ k) :
    Set.range (fun m => hyperplane xh θ (-⟪z m, θ - xh⟫)) =
      Set.range (fun m => hyperplane xh θ (-⟪z' m, θ - xh⟫)) := by sorry

end Arxiv1906_02008
