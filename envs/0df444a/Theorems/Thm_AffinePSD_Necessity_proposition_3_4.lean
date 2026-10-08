-- Prove2me | Theorems.Thm_AffinePSD_Necessity_proposition_3_4
-- name    : AffinePSD.Necessity.proposition_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:15.642022+00:00
-- url     : https://prove2.me/theorems/699796e0-03ed-44f8-9b6b-60a536e8a905
-- title:
--   Proposition 3.4 — every affine process on $S_d^+$ is Feller and regular
-- statement:
--   Let $X$ be an affine process with state space $S_d^+$, with transition family $p_t$ and exponents $\varphi,\psi$ in (2.1). Then:
--
--   1. $X$ is a Feller process: $(P_t)_{t\ge 0}$ is a strongly continuous contraction semigroup on $C_0(S_d^+)$;
--   2. $X$ is regular: the right derivatives
--   $$F(u) = \frac{\partial \varphi(t,u)}{\partial t}\Big|_{t=0+}, \qquad R(u) = \frac{\partial \psi(t,u)}{\partial t}\Big|_{t=0+}$$
--   exist for all $u \in S_d^+$ and are continuous at $u = 0$.
--
--   Regularity is what allows differentiating the semiflow identities (3.1)–(3.2) at $t = 0$, which produces the generalized Riccati equations; the Feller property gives the generator on $C_0(S_d^+)$.
--
--   **Formalization Note.** The Feller property uses the platform definition `EthierKurtz.IsStronglyContinuousContractionSemigroup` for operators on $C_0(S_d^+)$ that agree with $P_t$ for $t \ge 0$. Continuity of $F$ and $R$ at $0$ is continuity within $S_d^+$.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), Proposition 3.4, p. 17

import Mathlib
import Definitions.Def_AffinePSD_Necessity_Process

open MeasureTheory ProbabilityTheory

namespace AffinePSD.Necessity

/-- Proposition 3.4 (arXiv:0910.0137v3, §3, p. 17). Let `X` be an affine process with state space
`S_d^+`. Then (i) `X` is a Feller process, and (ii) `X` is regular.

**Formalization Note.** Feller: `(P_t)` restricts to a strongly continuous contraction semigroup on
`C_0(S_d^+)` (`EthierKurtz.IsStronglyContinuousContractionSemigroup`). Regular: the one-sided
derivatives (2.2) at `t = 0` exist for every `u ∈ S_d^+` and are continuous at `u = 0` within `S_d^+`. -/
theorem proposition_3_4 {d : ℕ} (p : ℝ → Kernel (Cone d) (Cone d)) (φ : ℝ → Mat d → ℝ)
    (ψ : ℝ → Mat d → Mat d) (hX : IsAffineWith p φ ψ) :
    IsFeller p ∧ IsRegular φ ψ := by sorry

end AffinePSD.Necessity
