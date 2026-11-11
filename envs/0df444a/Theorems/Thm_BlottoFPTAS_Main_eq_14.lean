-- Prove2me | Theorems.Thm_BlottoFPTAS_Main_eq_14
-- name    : BlottoFPTAS.Main.eq_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:40:57.226064+00:00
-- url     : https://prove2.me/theorems/839985a8-da63-4dbf-9e86-cdc05166d24a
-- title:
--   §5.2, Eq. (14) — the weighted CDF distance is the maximum of the signed-multiplier penalties
-- statement:
--   For positive weights $w$ summing to one and auxiliary marginals $p$ on a finite ordered code set,
--   $$\max_\lambda\ \lambda\cdot(F_p-F_x)=d_w(p,x)$$
--   for every code allocation $x$, the maximum over signed multipliers $\lambda$ being attained; the identity also holds with a distribution $\pi$ on code allocations in place of $x$. It turns the CDF distance into a maximum of linear penalties that multiplicative weights can update.
--
--   Differences from the source:
--   - generalization: code set I = {0, …, 2^Λ − 1}; x and π range over candidate and response allocations → any finite code set {0, …, N − 1} (N ≥ 1); any code allocation x and any distribution π on code allocations; reason: the identity uses only that the arguments are CDF families; the paper's case is N = 2^Λ restricted to X ∪ Y
--   - encoding: sign s ∈ {−1, 1}; max over λ → s a Boolean (true ↦ 1, false ↦ −1); IsGreatest of the set of penalties; reason: Lean convention
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), p. 37, §5.2, Eq. (14)

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_Learning

namespace BlottoFPTAS.Main

/-- **§5.2, Eq. (14)** (Bichler, Ghosh, arXiv:2611.05221, held version sha256 cac3638e…, p. 37).
For positive weights `w` summing to one and auxiliary marginals `p` on a finite ordered code set,
the maximum over signed multipliers `λ` of the penalty `λ · (F_p − F_x)` is attained and equals
`d_w(p, x)`, for every code allocation `x`; the identity also holds with a distribution `π` on
code allocations in place of `x`. -/
theorem eq_14 {m N : ℕ} (hN : 0 < N) (w : Fin m → ℝ) (hw : ∀ j, 0 < w j)
    (hsum : ∑ j, w j = 1) (p : Fin m → Fin N → ℝ) (hp : IsAux p) :
    (∀ x : Fin m → Fin N,
      IsGreatest
        {u : ℝ | ∃ l : Fin m → Bool × Fin N → ℝ, IsMult l ∧
          u = pair w l (fun j a => cdfAux p j a - cdfAlloc x j a)}
        (dW w (cdfAux p) (cdfAlloc x))) ∧
    (∀ π : (Fin m → Fin N) → ℝ, IsDist π →
      IsGreatest
        {u : ℝ | ∃ l : Fin m → Bool × Fin N → ℝ, IsMult l ∧
          u = pair w l (fun j a => cdfAux p j a - cdfDistr π j a)}
        (dW w (cdfAux p) (cdfDistr π))) := by sorry

end BlottoFPTAS.Main
