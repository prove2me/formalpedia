-- Prove2me | Theorems.Thm_FlatlyFoliated_theorem4_ellipticity
-- name    : FlatlyFoliated.theorem4_ellipticity
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T20:40:50.578247+00:00
-- url     : https://prove2.me/theorems/e13ca27a-496b-4c0e-8a8f-633ff52be713
-- title:
--   Theorem 4 — $\Lambda>0$ implies ellipticity (positive definiteness of $\Delta f\,\delta-Q$)
-- statement:
--   Let $\Lambda>0$, $\mu\ge0$, and let smooth $(f,\zeta,\eta)$ with $\eta>0$ solve the elliptic form (39)–(41) under the arrow-of-time convention $\Delta f/\eta>0$. Then:
--
--   1. at every point, the symmetric matrix $A_{ab}=\Delta f\,\delta_{ab}-Q_{ab}$ is positive definite: $\sum_{a,b}A_{ab}\nu_a\nu_b>0$ for all $\nu\ne0$;
--   2. if $\eta\ge\eta_{\min}>0$ and $|Q_{ab}\nu_a\nu_b|\le Q_{\max}$ for all unit vectors $\nu$ (the bounds (56)), then for every unit vector $\nu$
--   $$\sum_{a,b}A_{ab}\nu_a\nu_b\ \ge\ \sqrt{Q_{\max}^2+2\Lambda\eta_{\min}^2}-Q_{\max}>0 .$$
--
--   The matrix $A$ is the principal coefficient of the linearizations (61)–(63), so this is the (uniform) ellipticity of the FFR system on each slice.
--
--   **Formalization Note** The statement on a single slice uses constants $\eta_{\min},Q_{\max}$ (the paper allows them to depend on $t$). Ellipticity is encoded through the positive definiteness of the principal coefficient matrix, which is exactly what the paper's proof establishes.
-- source:
--   Bray, Hamm, Hirsch, Wheeler, Zhang, Flatly Foliated Relativity, arXiv:1911.00967v2, https://arxiv.org/abs/1911.00967, p. 13, Theorem 4 and its proof, eqs. (56)–(60)

import Mathlib
import Definitions.Def_FlatlyFoliatedRelativity_basic

open scoped ContDiff

namespace FlatlyFoliated

/-- Theorem 4 (core inequality (57)–(59)): for `Λ > 0`, `μ ≥ 0`, `η > 0` and the
arrow-of-time convention `Δf > 0`, the matrix `Δf·δ − Q` is positive definite, and uniformly
so under the bounds (56). -/
theorem theorem4_ellipticity (Λ : ℝ) (hΛ : 0 < Λ) (μ : R3 → ℝ) (J : R3 → R3)
    (f : R3 → ℝ) (ζ : R3 → R3) (η : R3 → ℝ) (hμ : ContDiff ℝ ∞ μ) (hJ : ContDiff ℝ ∞ J)
    (hf : ContDiff ℝ ∞ f) (hζ : ContDiff ℝ ∞ ζ) (hη : ContDiff ℝ ∞ η)
    (hμnn : ∀ x, 0 ≤ μ x) (hηpos : ∀ x, 0 < η x) (hconv : ∀ x, 0 < lap f x / η x)
    (hsys : EllipticSystem Λ μ J f ζ η) :
    (∀ (x ν : R3), ν ≠ 0 → 0 < ∑ a, ∑ b, ellCoeff f ζ a b x * ν a * ν b) ∧
    (∀ ηmin Qmax : ℝ, 0 < ηmin → (∀ x, ηmin ≤ η x) →
      (∀ (x ν : R3), ‖ν‖ = 1 → |∑ a, ∑ b, Qmat f ζ a b x * ν a * ν b| ≤ Qmax) →
      ∀ (x ν : R3), ‖ν‖ = 1 →
        Real.sqrt (Qmax ^ 2 + 2 * Λ * ηmin ^ 2) - Qmax ≤
          ∑ a, ∑ b, ellCoeff f ζ a b x * ν a * ν b) := by sorry

end FlatlyFoliated
