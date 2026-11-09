-- Prove2me | Theorems.Thm_CubeSampling_lemma_4_2
-- name    : CubeSampling.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:19:25.762712+00:00
-- url     : https://prove2.me/theorems/962d9cf4-a248-416f-abc0-af2fc0d28349
-- title:
--   Lemma 4.2 — a concentrating radial polynomial
-- statement:
--   **Lemma 4.2.** Fix $q_0 < 1/2$. There are $C_{q_0}$ and $L_0$ such that for all integers $\ell \ge L_0$ and $D$ with $\ell \le q_0 D$, there is a radial polynomial $p$ on $\{-1,1\}^D$ with $\mathbb E[p^2] = 1$ and exact degree $\ell$ such that
--   $$
--   \Bigl\|\bigl(S_D - 2\sqrt{\ell(D-\ell)}\bigr)p\Bigr\|_2 \le C_{q_0}\sqrt D\, \ell^{-1/6}.
--   $$
--
--   The energy distribution $p^2\,d\mu_D$ thus sits near the center $\tau = 2\sqrt{\ell(D-\ell)}$, far above the typical scale $\sqrt D$ of $S_D$.
--
--   Differences from the source:
--   - encoding: for all sufficiently large ℓ ≤ q₀D → ∃ L₀, ∀ ℓ ≥ L₀ with ℓ ≤ q₀D; reason: the threshold depends only on q₀, like the constant
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Lemma 4.2, p.17

import Mathlib
import Definitions.Def_CubeSampling_IsRadial
import Definitions.Def_CubeSampling_HasExactDegree
import Definitions.Def_CubeSampling_cubeMean
import Definitions.Def_CubeSampling_coordSum

namespace CubeSampling

/-- Lemma 4.2 (a concentrating polynomial) (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Lemma 4.2, p.17): fix `q₀ < 1/2`. For all
sufficiently large `ℓ ≤ q₀ D` there is a unit norm radial polynomial `p` of exact degree `ℓ` on
`{−1, 1}^D` with `‖(S_D − 2√(ℓ(D − ℓ))) p‖₂ ≤ C_{q₀} √D ℓ^{−1/6}`.

**Formalization Note** "Sufficiently large" is `∃ L₀, ∀ ℓ ≥ L₀`, with `C` and `L₀` depending on `q₀`
only; `‖g‖₂ = √(E[g²])`; `ℓ^{−1/6}` is a real power. -/
theorem lemma_4_2 (q₀ : ℝ) (hq₀ : q₀ < 1 / 2) :
    ∃ C : ℝ, ∃ L₀ : ℕ, ∀ D ℓ : ℕ, L₀ ≤ ℓ → (ℓ : ℝ) ≤ q₀ * D →
      ∃ p : Cube D → ℝ, IsRadial D p ∧ cubeMean D (fun x => p x ^ 2) = 1 ∧ HasExactDegree D ℓ p ∧
        Real.sqrt (cubeMean D (fun x =>
            ((coordSum D x : ℝ) - 2 * Real.sqrt ((ℓ : ℝ) * ((D : ℝ) - ℓ))) ^ 2 * p x ^ 2))
          ≤ C * Real.sqrt D * (ℓ : ℝ) ^ (-(1 : ℝ) / 6) := by sorry

end CubeSampling
