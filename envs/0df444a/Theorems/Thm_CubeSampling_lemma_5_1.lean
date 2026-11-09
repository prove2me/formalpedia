-- Prove2me | Theorems.Thm_CubeSampling_lemma_5_1
-- name    : CubeSampling.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:18:21.933475+00:00
-- url     : https://prove2.me/theorems/91fc8083-67bc-4d37-b939-bf6a3660993e
-- title:
--   Lemma 5.1 — radial-weight identity
-- statement:
--   **Lemma 5.1.** Let $0 \le r, s \le \lfloor d/2\rfloor$ be integers, $f \in H_{d,r}$, $g \in H_{d,s}$, and let $H$ be any real function of the coordinate sum. Then
--   $$
--   \mathbb E_{\mu_d}\bigl[f g\, H(S_d)\bigr] = \begin{cases} 0, & r \ne s,\\ \langle f, g\rangle_d\; \mathbb E_{\mu_{d-2r}}\bigl[H(S_{d-2r})\bigr], & r = s,\end{cases} \tag{12}
--   $$
--   where $\langle f, g\rangle_d = \mathbb E_{\mu_d}[fg]$ and $S_0 = 0$.
--
--   The identity transfers one-dimensional concentration to whole spaces of harmonic directions and keeps different harmonic degrees orthogonal under radial weights.
--
--   Differences from the source:
--   - encoding: H_{d,r} characterized by Σᵢ ∂ᵢ f = 0 → span{χ_S : |S| = r} ∩ {Σᵢ ∂ᵢ f = 0} with ∂ᵢ the discrete derivative (f(x^{i→1}) − f(x^{i→−1}))/2; reason: the discrete derivative is the multilinear partial derivative on the cube
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Lemma 5.1, (12), p.19

import Mathlib
import Definitions.Def_CubeSampling_IsHarmonic
import Definitions.Def_CubeSampling_cubeMean
import Definitions.Def_CubeSampling_coordSum

namespace CubeSampling

/-- Lemma 5.1 (radial-weight identity) (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Lemma 5.1, (12), p.19): for integers
`0 ≤ r, s ≤ ⌊d/2⌋`, `f ∈ H_{d,r}`, `g ∈ H_{d,s}` and any real function `H` of the coordinate sum,
`E_{μ_d}[f g H(S_d)] = 0` if `r ≠ s` and `= ⟨f, g⟩_d E_{μ_{d−2r}}[H(S_{d−2r})]` if `r = s`, where
`⟨f, g⟩_d = E_{μ_d}[fg]` and `S_0 = 0`. -/
theorem lemma_5_1 (d r s : ℕ) (hr : r ≤ d / 2) (hs : s ≤ d / 2) (f g : Cube d → ℝ)
    (hf : IsHarmonic d r f) (hg : IsHarmonic d s g) (H : ℤ → ℝ) :
    cubeMean d (fun x => f x * g x * H (coordSum d x)) =
      if r = s then
        cubeMean d (fun x => f x * g x) * cubeMean (d - 2 * r) (fun y => H (coordSum (d - 2 * r) y))
      else 0 := by sorry

end CubeSampling
