-- Prove2me | Theorems.Thm_AffinePSD_Necessity_proposition_4_18
-- name    : AffinePSD.Necessity.proposition_4_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:10.309506+00:00
-- url     : https://prove2.me/theorems/deca8e94-2448-4c04-a83e-09022ae0def8
-- title:
--   Proposition 4.18 — the drift condition (2.4): $b\succeq(d-1)\alpha$
-- statement:
--   Let $X$ be an affine process on $S_d^+$ with exponents $\varphi, \psi$, let $\chi$ be a truncation function, and let $(\alpha, b, \beta^{ij}, c, \gamma, m, \mu)$ be its parameters from Proposition 4.9: $\alpha, \beta^{ij}, c, \gamma, m, \mu$ satisfy the admissibility conditions of Definition 2.3, $b \in S_d^+$, and the right derivatives of $\varphi,\psi$ at $t = 0$ are given by (2.16)–(2.17). Then (2.4) holds:
--   $$b \succeq (d-1)\alpha.$$
--
--   This completes the admissibility of the parameter set: Propositions 4.9 and 4.18 together show that every affine process on $S_d^+$ has an admissible parameter set. For $d \ge 2$ the condition forces a nonzero constant drift whenever there is a diffusion component.
--
--   **Formalization Note.** $b \succeq (d-1)\alpha$ means $b - (d-1)\alpha \in S_d^+$, with $d - 1$ computed in $\mathbb R$. The parameters are hypotheses; since they are uniquely determined by $F$ and $R$, quantifying over them is the paper's statement about "the" parameters of $X$.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), Proposition 4.18, p. 36

import Mathlib
import Definitions.Def_AffinePSD_Necessity_Params
import Definitions.Def_AffinePSD_Necessity_Process

open MeasureTheory ProbabilityTheory

namespace AffinePSD.Necessity

/-- Proposition 4.18 (arXiv:0910.0137v3, §4.4, p. 36): let `X` be an affine process on `S_d^+`; then
(2.4) holds, that is, `b ⪰ (d − 1)α`.

Here `(α, b, β^{ij}, c, γ, m, μ)` are the parameters of `X` from Proposition 4.9: `α, β^{ij}, c, γ, m, μ`
admissible, `b ∈ S_d^+`, and `F`, `R` of (2.2) given by (2.16)–(2.17). Since these parameters are unique,
the universal quantification over them is the paper's statement.

**Formalization Note.** `b ⪰ (d − 1)α` is `PSD (b − (d − 1)α)`, with `d − 1` computed in `ℝ`. -/
theorem proposition_4_18 {d : ℕ} (χ : Trunc d) (p : ℝ → Kernel (Cone d) (Cone d))
    (φ : ℝ → Mat d → ℝ) (ψ : ℝ → Mat d → Mat d) (hX : IsAffineWith p φ ψ) (P : Params d)
    (hP : AdmissibleCore χ P) (hb : PSD P.b)
    (hFR : ∀ u : Mat d, PSD u →
      HasDerivWithinAt (fun t => φ t u) (Fpar P u) (Set.Ici 0) 0 ∧
      HasDerivWithinAt (fun t => ψ t u) (Rpar χ P u) (Set.Ici 0) 0) :
    PSD (P.b - ((d : ℝ) - 1) • P.α) := by sorry

end AffinePSD.Necessity
