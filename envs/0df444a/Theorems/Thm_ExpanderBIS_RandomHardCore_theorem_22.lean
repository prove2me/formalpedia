-- Prove2me | Theorems.Thm_ExpanderBIS_RandomHardCore_theorem_22
-- name    : ExpanderBIS.RandomHardCore.theorem_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:33:34.469434+00:00
-- url     : https://prove2.me/theorems/d05bb990-5eee-4c4c-ac26-c95238059d95
-- title:
--   Theorem 22 — Bassalygo's entropy criterion for bipartite expansion
-- statement:
--   Let $\mathcal G^{\mathrm{bip}}(m,\Delta)$ be the uniform family of labelled $\Delta$-regular bipartite graphs with sides of size $m$. Put $H_2(p)=-p\log_2 p-(1-p)\log_2(1-p)$. For $0<\sigma<1$, $\rho>1$, $\sigma\rho<1$, and $H_2(\sigma)-\sigma\rho H_2(1/\rho)>0$, suppose
--
--   $$\Delta>\frac{H_2(\sigma)+H_2(\sigma\rho)}{H_2(\sigma)-\sigma\rho H_2(1/\rho)}.$$
--
--   Then the fraction of graphs in $\mathcal G^{\mathrm{bip}}(m,\Delta)$ that are bipartite $(\sigma,\rho)$-expanders tends to one as $m\to\infty$. This cited criterion supplies the random graph input for Lemma 23.
--
--   **Formalization Note** The source states $0<\sigma<1$ and $\rho>0$ in Definition 21; the extra restrictions make both entropy arguments and the denominator meaningful. Bassalygo's original formulation warrants moderator review.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 23, Theorem 22 (citing Bassalygo [7])

import Mathlib
import Definitions.Def_ExpanderBIS_RandomHardCore_Setting

namespace ExpanderBIS.RandomHardCore

theorem theorem_22 (σ ρ : ℝ) (Δ : ℕ)
    (hσpos : 0 < σ) (hσlt : σ < 1) (hρ : 1 < ρ) (hσρ : σ * ρ < 1)
    (hden : 0 < H₂ σ - σ * ρ * H₂ (1 / ρ))
    (hΔ : (H₂ σ + H₂ (σ * ρ)) /
      (H₂ σ - σ * ρ * H₂ (1 / ρ)) < (Δ : ℝ)) :
    AlmostEvery Δ (fun _ G => IsSigmaRhoExpander G σ ρ) := by sorry

end ExpanderBIS.RandomHardCore
