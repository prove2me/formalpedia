-- Prove2me | Theorems.Thm_FairRandomObject_Bads_bh_antimonotone
-- name    : FairRandomObject.Bads.bh_antimonotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:51.962261+00:00
-- url     : https://prove2.me/theorems/e220535e-d591-4b24-981d-53693fadc4a8
-- title:
--   Remark after Definition 15, p. 16 — the shares ϕ¹_i(x) are anti-monotonic to the disutilities x_i
-- statement:
--   Let $n\ge2$ and $x\in\mathbb R^N_+$. For any two agents $i,k$,
--   $$x_i\le x_k\ \Longrightarrow\ \varphi^1_k(x)\le\varphi^1_i(x).$$
--   That is, the Bottom-Heavy rule never gives a larger share to an agent with a larger disutility.
--
--   Combined with Chebyshev's sum inequality, this shows that $\varphi^1$ has social cost at most that of Equal Split, the case $\theta=0$ of the proof of Theorem 17.
-- source:
--   Bogomolnaia, Moulin, Sandomirskiy, On the Fair Division of a Random Object, arXiv:1903.10361v4, p. 16, remark after Definition 15

import Mathlib
import Definitions.Def_FairRandomObject_Bads_Setting
import Definitions.Def_FairRandomObject_Bads_BottomHeavy

namespace FairRandomObject.Bads

/-- Bogomolnaia, Moulin, Sandomirskiy, On the Fair Division of a Random Object, arXiv:1903.10361v4, p. 16, remark after Definition 15: the shares `ϕ¹_i(x)` of the
Bottom-Heavy rule are anti-monotonic to the disutilities `x_i`: if `x_i ≤ x_k` then
`ϕ¹_k(x) ≤ ϕ¹_i(x)`, for every `x ∈ ℝ^N_+`. -/
theorem bh_antimonotone {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (hx : 0 ≤ x) (i k : Fin n)
    (hik : x i ≤ x k) : bottomHeavy n 1 x k ≤ bottomHeavy n 1 x i := by sorry

end FairRandomObject.Bads
