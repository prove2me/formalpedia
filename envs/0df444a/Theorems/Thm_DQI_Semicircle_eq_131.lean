-- Prove2me | Theorems.Thm_DQI_Semicircle_eq_131
-- name    : DQI.Semicircle.eq_131
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:27.675732+00:00
-- url     : https://prove2.me/theorems/be568cca-c570-4420-852e-28863d984900
-- title:
--   (131), p. 34 — if 2ℓ + 1 < d⊥ then ⟨s^(m,ℓ)⟩_opt/m = ρ + √(ρ(1 − ρ)) λ_max^(m,ℓ,d)/m
-- statement:
--   Let $p$ be prime, $B\in\mathbb F_p^{m\times n}$ with $m>n$, and $|F_i|=r$ for all $i$ with $1\le r\le p-1$; put $\rho=r/p$ and $d=(p-2r)/\sqrt{r(p-r)}$. If $2\ell+1<d^\perp$, then the optimal expected number of satisfied constraints over normalized DQI states $|P(f)\rangle$ with $\deg P\le\ell$ satisfies
--   $$\frac{\langle s^{(m,\ell)}\rangle_{\rm opt}}{m}=\rho+\sqrt{\rho(1-\rho)}\,\frac{\lambda_{\max}^{(m,\ell,d)}}{m},$$
--   where $\lambda_{\max}^{(m,\ell,d)}$ is the largest eigenvalue of $A^{(m,\ell,d)}$.
--
--   This is the exact finite-size form of Theorem 4.1: the asymptotics reduce to those of $\lambda_{\max}$.
-- source:
--   Jordan et al., Optimization by Decoded Quantum Interferometry, arXiv:2408.08292v5, p. 34, §9.4, (131)

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting

namespace DQI.Semicircle

/-- (131), p. 34: `⟨s^{(m,ℓ)}⟩_opt / m = ρ + √(ρ(1−ρ)) λ_max^{(m,ℓ,d)} / m`, `ρ = r/p`. -/
theorem eq_131 (p : ℕ) [Fact p.Prime] (m n : ℕ) (B : Matrix (Fin m) (Fin n) (ZMod p))
    (F : Fin m → Finset (ZMod p)) (r : ℕ) (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p)
    (hnm : n < m) (ℓ : ℕ) (hdist : DistGt B (2 * ℓ + 1)) :
    optSat B F ℓ / m =
      (r : ℝ) / p + Real.sqrt ((r : ℝ) / p * (1 - (r : ℝ) / p)) * lamMax (Atri m ℓ (dparOf p r)) / m := by sorry

end DQI.Semicircle
