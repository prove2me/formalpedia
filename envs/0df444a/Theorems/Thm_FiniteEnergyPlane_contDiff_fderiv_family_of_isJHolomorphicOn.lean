-- Prove2me | Theorems.Thm_FiniteEnergyPlane_contDiff_fderiv_family_of_isJHolomorphicOn
-- name    : FiniteEnergyPlane.contDiff_fderiv_family_of_isJHolomorphicOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-08T22:42:19.053189+00:00
-- url     : https://prove2.me/theorems/7b437918-1f87-4e93-921f-11efc4f17200
-- title:
--   Smoothness of the parameter derivative of a family of holomorphic maps
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be strictly star-shaped, $J$ a compatible complex structure on $\xi$, and $\tilde J$ the induced almost complex structure on $\mathbb R^{2n+2}\setminus\{0\}$. Let $l\ge 2$, $r\in\mathbb R$, and let $g:\mathbb C\times\mathbb R\to\mathbb R^{2n+2}$ be of class $C^l$ on $\mathbb C\times(-r,r)$, such that for every $t\in(-r,r)$ the map $g(\cdot,t)$ is smooth, avoids $0$ and is $\tilde J$-holomorphic on $\mathbb C$. Then for every $t\in(-r,r)$ the map $z\mapsto\partial_t g(z,t)$ is smooth.
--
--   The statement upgrades the regularity of the parameter derivative of a family of holomorphic maps, so that infinitesimal deformations of a holomorphic plane can be treated as smooth sections.
--
--   Formalization Note: $\partial_t g(z,t)$ is `fderiv ℝ g (z, t) (0, 1)`; `JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ f` means $f$ is differentiable and $\partial_s f+\tilde J(f)\,\partial_t f=0$ on $\mathbb C$.
-- source:
--   McDuff-Salamon, J-holomorphic curves and symplectic topology (2012), Appendix B (elliptic regularity); Hryniewicz, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open scoped ContDiff

/-- Let `g : ℂ × ℝ → V n` be `C^l` with `l ≥ 2` on `ℂ × (-r, r)`, and let every `g(·, t)`,
`t ∈ (-r, r)`, be smooth, avoid `0` and be `J̃`-holomorphic on `ℂ`. Then the `t`-derivative
`z ↦ ∂ₜg(z, t)` is smooth for every `t ∈ (-r, r)`. -/
theorem contDiff_fderiv_family_of_isJHolomorphicOn {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (l : ℕ) (hl : 2 ≤ l) (r : ℝ) (g : ℂ × ℝ → V n)
    (hg : ContDiffOn ℝ l g (Set.univ ×ˢ Set.Ioo (-r) r))
    (hmem : ∀ t ∈ Set.Ioo (-r) r, ContDiff ℝ ∞ (fun z => g (z, t)) ∧ (∀ z, g (z, t) ≠ 0) ∧
      JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ (fun z => g (z, t))) :
    ∀ t ∈ Set.Ioo (-r) r, ContDiff ℝ ∞ (fun z => fderiv ℝ g (z, t) (0, 1)) := by
  sorry

end FiniteEnergyPlane
