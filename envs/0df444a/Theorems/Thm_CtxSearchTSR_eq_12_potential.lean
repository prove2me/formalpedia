-- Prove2me | Theorems.Thm_CtxSearchTSR_eq_12_potential
-- name    : CtxSearchTSR.eq_12_potential
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:21.884244+00:00
-- url     : https://prove2.me/theorems/d77894ab-ca54-4d2c-9884-5be395bf9a43
-- title:
--   (12) — the potential $\Phi$ is non-negative and $\Phi_1=\sqrt d+\sqrt d\|z\|_2^2\le2\sqrt d$
-- statement:
--   For the potential $\Phi(\mathbf m,R,\mathbf z)=\operatorname{Tr}R+(\mathbf z-\mathbf m)^\top R^{-1}(\mathbf z-\mathbf m)$ of (12):
--
--   1. $\Phi(\mathbf m,R,\mathbf z)\ge0$ whenever $R\succ0$;
--   2. at the initial state (8), $\mathbf m_1=0$, $R_1=I_d/\sqrt d$:
--   $$\Phi_1=\sqrt d+\sqrt d\,\|\mathbf z\|_2^2;$$
--   3. if $\|\mathbf z\|_2\le1$, then $\sqrt d+\sqrt d\,\|\mathbf z\|_2^2\le2\sqrt d$.
--
--   Together with Lemma 2.5 this gives $\sum_{t=1}^T\mathbb E[\ell_t]\le6\Phi_1\le12\sqrt d$.
--
--   Differences from the source:
--   - generalization: Φ_t (reachable states) is non-negative, and Φ₁ = √d + √d‖z‖₂² for the hidden target → Φ(m, R, z) ≥ 0 for every R ≻ 0 and all m, z; the value of Φ₁ for every z; reason: reachable states have R ≻ 0 (§2.2); the bound ≤ 2√d keeps the paper's ‖z‖₂ ≤ 1; it specializes to the paper's case
-- source:
--   Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, Contextual Search and Bilateral Trade with a Trace-Square-Root Potential, STOC 2027 submission manuscript (sha256 70eeb0d19227c9eee557cdff5598f97062f442373fcde3a3eb76a6cb65a2ad6c), proof of Theorem 2.4, p.11, (12)

import Mathlib
import Definitions.Def_CtxSearchTSR_Algorithm2
import Definitions.Def_CtxSearchTSR_Potentials

open Matrix

namespace CtxSearchTSR

/-- **The potential (12): non-negativity and initial value.** Cosson et al., *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*, STOC 2027
submission (manuscript sha256 70eeb0d1…), proof of
Theorem 2.4, p.11.

"For a fixed hidden target, we consider the non-negative potential defined by
Φ_t = Φ(m_t, R_t, z) = Tr R_t + (z − m_t)ᵀR_t⁻¹(z − m_t). (12) At initialization, the potential
satisfies Φ₁ = √d + √d‖z‖₂² ≤ 2√d."

1. Φ(**m**, R, **z**) ≥ 0 whenever R ≻ 0.
2. At the initial state (8), Φ₁ = √d + √d ‖**z**‖₂².
3. If ‖**z**‖₂ ≤ 1, then √d + √d ‖**z**‖₂² ≤ 2√d.

**Formalization Note.** ‖·‖₂ is the Euclidean norm `eucNorm`. At d = 0 both sides of 2 are 0. -/
theorem eq_12_potential {d : ℕ} :
    (∀ (m z : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ), R.PosDef → 0 ≤ Phi m R z) ∧
    (∀ z : Fin d → ℝ, Phi (State.init d).m (State.init d).R z =
      Real.sqrt d + Real.sqrt d * eucNorm z ^ 2) ∧
    (∀ z : Fin d → ℝ, eucNorm z ≤ 1 →
      Real.sqrt d + Real.sqrt d * eucNorm z ^ 2 ≤ 2 * Real.sqrt d) := by sorry

end CtxSearchTSR
