-- Prove2me | Theorems.Thm_AffinePSD_Necessity_proposition_4_9
-- name    : AffinePSD.Necessity.proposition_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:31.086317+00:00
-- url     : https://prove2.me/theorems/b6eea56e-8a1e-47c4-826d-212666117124
-- title:
--   Proposition 4.9 — $F$ and $R$ have the form (2.16)–(2.17) for admissible parameters with $b\in S_d^+$
-- statement:
--   Let $X$ be an affine process with state space $S_d^+$, exponents $\varphi, \psi$ in (2.1), and let $\chi$ be a truncation function. Then there exist parameters $(\alpha, b, \beta^{ij}, c, \gamma, m, \mu)$, where $\alpha, \beta^{ij}, c, \gamma, m, \mu$ satisfy the admissibility conditions of Definition 2.3 and $b \in S_d^+$, such that for every $u \in S_d^+$ the right derivatives (2.2) are
--   $$F(u) = \langle b,u\rangle + c - \int_{S_d^+\setminus\{0\}}\big(e^{-\langle u,\xi\rangle}-1\big)\,m(d\xi), \qquad (2.16)$$
--   $$R(u) = -2u\alpha u + B^\top(u) + \gamma - \int_{S_d^+\setminus\{0\}} \frac{e^{-\langle u,\xi\rangle} - 1 + \langle\chi(\xi),u\rangle}{\|\xi\|^2\wedge1}\,\mu(d\xi). \qquad (2.17)$$
--
--   At this stage only $b \in S_d^+$ is obtained, not the drift condition (2.4) $b \succeq (d-1)\alpha$ (Remark 4.10); that is Proposition 4.18.
--
--   **Formalization Note.** "Admissible except (2.4)" is the predicate `AdmissibleCore`; $\mu$ is encoded by a finite measure $\nu$ and a positive semidefinite density $H$. The derivatives at $t = 0$ are one-sided, within $[0,\infty)$. As a guard against Lean's convention that the integral of a non-integrable function is $0$, the integrands of (2.16)–(2.17) are also concluded integrable at every $u \in S_d^+$.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), Proposition 4.9 and Remark 4.10, p. 23

import Mathlib
import Definitions.Def_AffinePSD_Necessity_Params
import Definitions.Def_AffinePSD_Necessity_Process

open MeasureTheory ProbabilityTheory

namespace AffinePSD.Necessity

/-- Proposition 4.9 (arXiv:0910.0137v3, §4.1, p. 23). Let `X` be an affine process with state space
`S_d^+` and `χ` a truncation function. Then there exist parameters `(α, b, β^{ij}, c, γ, m, μ)`, where
`α, β^{ij}, c, γ, m, μ` satisfy the admissibility conditions of Definition 2.3 and `b ∈ S_d^+`, such that
the functions `F` and `R` of (2.2) are of the form (2.16) and (2.17).

**Formalization Note.** `F(u)`, `R(u)` are the one-sided `t`-derivatives of `φ(t,u)`, `ψ(t,u)` at
`t = 0` (2.2), stated for every `u ∈ S_d^+`. `AdmissibleCore` is Definition 2.3 without (2.4)
(Remark 4.10: at this stage only `b ∈ S_d^+` is obtained). `μ` is encoded by `(ν, H)` (see `Params`).
Junk-integral guard: the integrands of (2.16)–(2.17) are also concluded integrable at every PSD `u`. -/
theorem proposition_4_9 {d : ℕ} (χ : Trunc d) (p : ℝ → Kernel (Cone d) (Cone d))
    (φ : ℝ → Mat d → ℝ) (ψ : ℝ → Mat d → Mat d) (hX : IsAffineWith p φ ψ) :
    ∃ P : Params d, AdmissibleCore χ P ∧ PSD P.b ∧
      ∀ u : Mat d, PSD u →
        HasDerivWithinAt (fun t => φ t u) (Fpar P u) (Set.Ici 0) 0 ∧
        HasDerivWithinAt (fun t => ψ t u) (Rpar χ P u) (Set.Ici 0) 0 ∧
        IntegrableFR χ P u := by sorry

end AffinePSD.Necessity
