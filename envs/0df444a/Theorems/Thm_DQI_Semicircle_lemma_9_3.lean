-- Prove2me | Theorems.Thm_DQI_Semicircle_lemma_9_3
-- name    : DQI.Semicircle.lemma_9_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:22.140013+00:00
-- url     : https://prove2.me/theorems/940563d2-3ed2-48df-b27c-b18c1ba66902
-- title:
--   Lemma 9.3, p. 32 — if ℓ ≤ m/2 and d ≥ −(m − 2ℓ)/√(ℓ(m − ℓ)), then λ_max^(m,ℓ,d)/m → μd + 2√(μ(1 − μ)) as m, ℓ → ∞ with ℓ/m = μ
-- statement:
--   Let $\mu>0$ and $d\in\mathbb R$. Let $(m_j,\ell_j)_{j\ge0}$ be any sequence of sizes with $m_j\to\infty$ and $\ell_j/m_j\to\mu$, and suppose that for every $j$, $\ell_j\le m_j/2$ and (when $\ell_j\ge1$)
--   $$d\ \ge\ -\frac{m_j-2\ell_j}{\sqrt{\ell_j(m_j-\ell_j)}} .$$
--   Then
--   $$\lim_{j\to\infty}\frac{\lambda_{\max}^{(m_j,\ell_j,d)}}{m_j}=\mu d+2\sqrt{\mu(1-\mu)} .$$
--
--   This gives the asymptotics of the eigenvalue in (131), hence the semicircle curve of Theorem 4.1.
--
--   **Formalization Note** "$m,\ell\to\infty$ with $\ell/m=\mu$ fixed" is encoded as an arbitrary sequence with $m_j\to\infty$ and $\ell_j/m_j\to\mu$; $\mu>0$ makes $\ell_j\to\infty$ too. The hypothesis on $d$ is required only when $\ell_j\ge1$ (for $\ell_j=0$ it would divide by zero).
-- source:
--   Jordan et al., Optimization by Decoded Quantum Interferometry, arXiv:2408.08292v5, p. 32, Lemma 9.3, (113)

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting

namespace DQI.Semicircle

/-- Lemma 9.3, p. 32. The limit is along any sequence of sizes `m_j → ∞` with `ℓ_j/m_j → μ`. -/
theorem lemma_9_3 (μ dpar : ℝ) (hμ : 0 < μ) (m ℓ : ℕ → ℕ)
    (hratio : Filter.Tendsto (fun j => (ℓ j : ℝ) / (m j : ℝ)) Filter.atTop (nhds μ))
    (hm : Filter.Tendsto m Filter.atTop Filter.atTop) (hℓm : ∀ j, 2 * ℓ j ≤ m j)
    (hd : ∀ j, 0 < ℓ j → -((m j : ℝ) - 2 * ℓ j) / Real.sqrt (ℓ j * ((m j : ℝ) - ℓ j)) ≤ dpar) :
    Filter.Tendsto (fun j => lamMax (Atri (m j) (ℓ j) dpar) / m j) Filter.atTop
      (nhds (μ * dpar + 2 * Real.sqrt (μ * (1 - μ)))) := by sorry

end DQI.Semicircle
