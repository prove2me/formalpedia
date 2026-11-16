-- Prove2me | Theorems.Thm_FiniteSampleDependence_Rigidity_Supplement_qmi_four_sample_unbiased
-- name    : FiniteSampleDependence.Rigidity.Supplement.qmi_four_sample_unbiased
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:52:41.355795+00:00
-- url     : https://prove2.me/theorems/174b5986-fb25-4cca-8660-600451b6265b
-- title:
--   Lemma 7.2 — the four-task payment $M_{\mathrm{QMI}}$ is an unbiased estimator of $F_{\mathrm{QMI}}$
-- statement:
--   Let $n,m\ge2$ and $U\in\Delta_{n,m}$. If $Z_t=(x_t,y_t)$, $t=1,\dots,4$, are i.i.d. with joint distribution $U$, then the four-task payment of equation (8),
--   $$M_{\mathrm{QMI}}=\mathbf 1\{x_1=x_2,\,y_1=y_2\}-2\cdot\mathbf 1\{x_1=x_2,\,y_1=y_3\}+\mathbf 1\{x_1=x_2,\,y_3=y_4\},$$
--   satisfies
--   $$\mathbb E_{U^{\otimes4}}[M_{\mathrm{QMI}}]=F_{\mathrm{QMI}}(U)=\sum_{i,\alpha}\big(U_{i\alpha}-r_i(U)c_\alpha(U)\big)^2.$$
--
--   The payment uses only equality comparisons of reports, so a mechanism paying it needs no estimate of the unknown distribution.
--
--   Differences from the source:
--   - encoding: standing assumption n, m ≥ 2 (Section 2, 'Throughout, n, m ≥ 2') → explicit hypotheses 2 ≤ n and 2 ≤ m; reason: the section's standing assumption written into the binders
--   - encoding: row indices 1..n, column indices 1..m → Fin n and Fin m (zero-based); reason: relabelling of indices; no instance changes
--   - encoding: the i.i.d. expectation E_{V^{⊗ℓ}}[M] of a payment rule → the exact finite sum Σ_{z ∈ ([n]×[m])^ℓ} M(z) ∏_t V_{x_t y_t} (expectedPayment), the paper's equation (6); reason: for finitely many outcomes the expectation is this sum; no measure-theoretic model is introduced
--   - encoding: sample indices 1, 2, 3, 4 → Fin 4 indices 0, 1, 2, 3; reason: relabelling of indices
-- source:
--   Yuqing Kong, Limits of Finite-Sample Dependence Measures under Data Processing Inequality, STOC 2027 submission #152 (October 2026; SHA-256 f5e620d74cb49d294e046590e96036aa28bf617d4b212a292b7bb68435363118), Lemma 7.2, PDF p. 19 (printed p. 18); eq. (8), same page; eq. (7), PDF p. 18

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model
import Definitions.Def_FiniteSampleDependence_Rigidity_Supplement_Model

namespace FiniteSampleDependence.Rigidity.Supplement

/-- Lemma 7.2 (Four-sample unbiased estimation for QMI), PDF p. 19 (printed p. 18). For i.i.d.
`Z₁,…,Z₄` with joint distribution `U ∈ Δ_{n,m}`, `E_{U^{⊗4}}[M_QMI] = F_QMI(U)`. -/
theorem qmi_four_sample_unbiased {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) :
    ∀ U ∈ simplex n m, expectedPayment (qmiPayment (n := n) (m := m)) U = qmi U := by sorry

end FiniteSampleDependence.Rigidity.Supplement
