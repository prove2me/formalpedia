-- Prove2me | Theorems.Thm_FiniteSampleDependence_Rigidity_Supplement_qmi_restricted_monotonicity
-- name    : FiniteSampleDependence.Rigidity.Supplement.qmi_restricted_monotonicity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:52:12.545197+00:00
-- url     : https://prove2.me/theorems/a803c33b-b3ca-4317-bbcc-46b85d3a5aa1
-- title:
--   Proposition 7.1 — restricted monotonicity: $F_{\mathrm{QMI}}(TU)\le\lambda^2F_{\mathrm{QMI}}(U)\le F_{\mathrm{QMI}}(U)$ for $T=\lambda D+(1-\lambda)q\mathbf 1^\top\in C_n$
-- statement:
--   Let $n,m\ge2$ and $F_{\mathrm{QMI}}(U)=\sum_{i,\alpha}(U_{i\alpha}-r_i(U)c_\alpha(U))^2$.
--
--   1. **Left processing.** For every $U\in\Delta_{n,m}$, every $\lambda\in[0,1]$, every doubly stochastic $D\in\mathbb R^{n\times n}$ and every probability vector $q\in\mathbb R^n$, the channel $T=\lambda D+(1-\lambda)q\mathbf 1_n^\top\in C_n$ satisfies
--   $$F_{\mathrm{QMI}}(TU)\le\lambda^2F_{\mathrm{QMI}}(U)\le F_{\mathrm{QMI}}(U).$$
--   2. **Right processing.** For every $U\in\Delta_{n,m}$, every $\mu\in[0,1]$, every doubly stochastic $D'\in\mathbb R^{m\times m}$ and every probability vector $p\in\mathbb R^m$, the channel $S=\mu D'+(1-\mu)p\mathbf 1_m^\top\in C_m$ satisfies
--   $$F_{\mathrm{QMI}}(US^\top)\le\mu^2F_{\mathrm{QMI}}(U)\le F_{\mathrm{QMI}}(U).$$
--
--   The bound holds for every representation of the channel in this form. Every channel in $C_n=\operatorname{conv}(DS_n\cup R1_n)$ has such a representation, so QMI is monotone under relabelings and signal-independent reports, though not under arbitrary channels.
--
--   Differences from the source:
--   - encoding: standing assumption n, m ≥ 2 (Section 2, 'Throughout, n, m ≥ 2') → explicit hypotheses 2 ≤ n and 2 ≤ m; reason: the section's standing assumption written into the binders
--   - encoding: row indices 1..n, column indices 1..m → Fin n and Fin m (zero-based); reason: relabelling of indices; no instance changes
--   - encoding: T ∈ C_n represented as above (T = λD + (1−λ)q1ₙᵀ, 0 ≤ λ ≤ 1, D ∈ DS_n) → λ, D ∈ doublyStochastic ℝ (Fin n) and q ∈ stdSimplex ℝ (Fin n) quantified, with T formed from them; reason: the inequality is stated for every representation, which is what 'represented as above' quantifies over
--   - encoding: the analogous inequality for right processing by S ∈ C_m → F_QMI(U Sᵀ) ≤ μ² F_QMI(U) ≤ F_QMI(U) for S = μD' + (1−μ)p1ₘᵀ; reason: right processing of U by a column-stochastic S is U ↦ USᵀ, as in (TF-DPI) and the report law TPSᵀ of §6
-- source:
--   Yuqing Kong, Limits of Finite-Sample Dependence Measures under Data Processing Inequality, STOC 2027 submission #152 (October 2026; SHA-256 f5e620d74cb49d294e046590e96036aa28bf617d4b212a292b7bb68435363118), Proposition 7.1, PDF p. 18 (printed p. 17); C_n and the representation T = λD + (1−λ)q1ᵀ, §7.2, same page

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model
import Definitions.Def_FiniteSampleDependence_Rigidity_Supplement_Model

namespace FiniteSampleDependence.Rigidity.Supplement

open Matrix

/-- Proposition 7.1 (Restricted monotonicity), PDF p. 18 (printed p. 17). For every
`U ∈ Δ_{n,m}` and every channel `T = λD + (1−λ) q 1ₙᵀ ∈ C_n` (`0 ≤ λ ≤ 1`, `D` doubly
stochastic, `q` a probability vector), `F_QMI(TU) ≤ λ² F_QMI(U) ≤ F_QMI(U)`; analogously, for
right processing by `S = μD' + (1−μ) p 1ₘᵀ ∈ C_m`, `F_QMI(USᵀ) ≤ μ² F_QMI(U) ≤ F_QMI(U)`. -/
theorem qmi_restricted_monotonicity {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) :
    (∀ U ∈ simplex n m, ∀ (lam : ℝ), 0 ≤ lam → lam ≤ 1 →
      ∀ D ∈ doublyStochastic ℝ (Fin n), ∀ q ∈ stdSimplex ℝ (Fin n),
        qmi ((lam • D + (1 - lam) • rankOneChannel q) * U) ≤ lam ^ 2 * qmi U ∧
          lam ^ 2 * qmi U ≤ qmi U) ∧
    (∀ U ∈ simplex n m, ∀ (mu : ℝ), 0 ≤ mu → mu ≤ 1 →
      ∀ D ∈ doublyStochastic ℝ (Fin m), ∀ p ∈ stdSimplex ℝ (Fin m),
        qmi (U * (mu • D + (1 - mu) • rankOneChannel p)ᵀ) ≤ mu ^ 2 * qmi U ∧
          mu ^ 2 * qmi U ≤ qmi U) := by sorry

end FiniteSampleDependence.Rigidity.Supplement
