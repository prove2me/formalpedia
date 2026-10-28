-- Prove2me | Theorems.Thm_DirectFidelity_State_eq_18
-- name    : DirectFidelity.State.eq_18
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:49.205973+00:00
-- url     : https://prove2.me/theorems/ea141b6f-b228-4470-bc79-6bee85e04e74
-- title:
--   (18), p. 6 — with $m_i$ as in (6), $C = \sum_i 4/(\ell^2 m_i d\chi_\rho(k_i)^2) \le 2\varepsilon^2/\log(2/\delta)$
-- statement:
--   Let $\rho$ be any $d\times d$ matrix, $d = 2^n$, let $0<\varepsilon$, $0<\delta<1$, $\ell\ge1$, and fix Pauli labels $k_1,\dots,k_\ell$ with $\chi_\rho(k_i)\ne0$. Take the copy numbers of (6),
--   $$m_i = \Big\lceil\frac{2}{d\,\chi_\rho(k_i)^2\,\ell\,\varepsilon^2}\log(2/\delta)\Big\rceil ,$$
--   and Hoeffding's constant $C = \sum_{i}\sum_{j\le m_i}(2c_i)^2$, $c_i = 1/(\ell m_i\sqrt d\,\chi_\rho(k_i))$. Then
--   $$C = \sum_{i=1}^{\ell}\frac{4}{\ell^2 m_i\, d\,\chi_\rho(k_i)^2} \le \frac{2\varepsilon^2}{\log(2/\delta)} .$$
--
--   Combined with (16) at $t = \varepsilon$, this gives failure probability at most $2\exp(-\log(2/\delta)) = \delta$, i.e. (8).
--
--   **Formalization Note.** The hypothesis $\delta < 1$ is added: it makes $\log(2/\delta) > 0$. For $\delta > 2$ every $m_i$ is $0$, so $C = 0$, while the right-hand side is negative and the inequality fails; the page treats $\delta$ as a failure probability, $0<\delta<1$, throughout.
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, p. 6, §Bounding the Failure Probabilities, (18)

import Mathlib
import Definitions.Def_DirectFidelity_State_Setting

namespace DirectFidelity.State

theorem eq_18 (n ℓ : ℕ) (ρ : Matrix (Q n) (Q n) ℂ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hℓ : 0 < ℓ) (ks : Fin ℓ → P n) (hks : ∀ i, chi ρ (ks i) ≠ 0) :
    Chof ρ ks (mVec ρ ε δ ks) =
        ∑ i, 4 / ((ℓ : ℝ) ^ 2 * (mVec ρ ε δ ks i : ℝ) * dim n * chi ρ (ks i) ^ 2) ∧
      Chof ρ ks (mVec ρ ε δ ks) ≤ 2 * ε ^ 2 / Real.log (2 / δ) := by sorry

end DirectFidelity.State
