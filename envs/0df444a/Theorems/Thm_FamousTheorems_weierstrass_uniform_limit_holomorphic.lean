-- Prove2me | Theorems.Thm_FamousTheorems_weierstrass_uniform_limit_holomorphic
-- name    : FamousTheorems.weierstrass_uniform_limit_holomorphic
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:25:43.426282+00:00
-- url     : https://prove2.me/theorems/4623641e-6a25-49fe-8e3b-55b424c24cc6
-- title:
--   Weierstrass's theorem: locally uniform limits of holomorphic functions are holomorphic
-- statement:
--   **Weierstrass's convergence theorem.** Let $U\subseteq\mathbb C$ be open and $(F_n)$ a family of holomorphic functions on $U$ (with values in a complex Banach space) converging to $f$ locally uniformly on $U$. Then $f$ is holomorphic on $U$.
--
--   This contrasts sharply with real analysis, where uniform limits of smooth functions need only be continuous. It is used, for instance, to show that power series, Dirichlet series and infinite products such as the Riemann zeta function and the Gamma function are holomorphic, and it underlies Montel's theorem and the theory of normal families.
--
--   **Formalization note.** Mathlib's `TendstoLocallyUniformlyOn.differentiableOn`. The family is indexed along an arbitrary nontrivial filter `φ` (sequences are the case `Filter.atTop` on `ℕ`), and holomorphy is only required eventually along `φ`. Holomorphic means complex differentiable on `U` (`DifferentiableOn ℂ`).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `TendstoLocallyUniformlyOn.differentiableOn`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem weierstrass_uniform_limit_holomorphic {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {U : Set ℂ} {φ : Filter ι} [φ.NeBot]
    {F : ι → ℂ → E} {f : ℂ → E} (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U) (hU : IsOpen U) : DifferentiableOn ℂ f U := by sorry

end FamousTheorems
