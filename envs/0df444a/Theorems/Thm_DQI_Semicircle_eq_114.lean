-- Prove2me | Theorems.Thm_DQI_Semicircle_eq_114
-- name    : DQI.Semicircle.eq_114
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:20.678637+00:00
-- url     : https://prove2.me/theorems/8048d9ff-b434-466a-a34f-0f17e9071786
-- title:
--   (114), p. 32 — for ℓ = μm ≤ m/2, eventually λ_max^(m,ℓ,d)/m ≥ μd + 2√(μ(1 − μ)) − ε
-- statement:
--   Let $\mu>0$ and $d\in\mathbb R$, and let $(m_j,\ell_j)$ be a sequence of sizes with $m_j\to\infty$, $\ell_j/m_j\to\mu$ and $\ell_j\le m_j/2$. Then for every $\varepsilon>0$, for all sufficiently large $j$,
--   $$\frac{\lambda_{\max}^{(m_j,\ell_j,d)}}{m_j}\ \ge\ \mu d+2\sqrt{\mu(1-\mu)}-\varepsilon .$$
--   That is, $\liminf_j\lambda_{\max}^{(m_j,\ell_j,d)}/m_j\ge\mu d+2\sqrt{\mu(1-\mu)}$, the lower half of Lemma 9.3.
--
--   **Formalization Note** The page writes "$\lim\ldots\ge$" before the limit is known to exist; the statement is the $\liminf$ reading, written with an explicit $\varepsilon$.
-- source:
--   Jordan et al., Optimization by Decoded Quantum Interferometry, arXiv:2408.08292v5, p. 32, proof of Lemma 9.3, (114)

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting

namespace DQI.Semicircle

/-- (114), p. 32 (lower bound in the proof of Lemma 9.3): for every `ε > 0`, eventually
`λ_max^{(m,ℓ,d)}/m ≥ μd + 2√(μ(1−μ)) − ε`. -/
theorem eq_114 (μ dpar : ℝ) (hμ : 0 < μ) (m ℓ : ℕ → ℕ)
    (hratio : Filter.Tendsto (fun j => (ℓ j : ℝ) / (m j : ℝ)) Filter.atTop (nhds μ))
    (hm : Filter.Tendsto m Filter.atTop Filter.atTop) (hℓm : ∀ j, 2 * ℓ j ≤ m j) :
    ∀ ε > 0, ∀ᶠ j in Filter.atTop,
      μ * dpar + 2 * Real.sqrt (μ * (1 - μ)) - ε ≤ lamMax (Atri (m j) (ℓ j) dpar) / m j := by sorry

end DQI.Semicircle
