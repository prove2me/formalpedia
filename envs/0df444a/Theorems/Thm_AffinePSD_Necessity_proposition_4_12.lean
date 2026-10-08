-- Prove2me | Theorems.Thm_AffinePSD_Necessity_proposition_4_12
-- name    : AffinePSD.Necessity.proposition_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:50:04.396998+00:00
-- url     : https://prove2.me/theorems/870b6003-827e-4ee3-a76a-56712b93a995
-- title:
--   Proposition 4.12 — the generator satisfies $\mathcal S_+\subset D(\mathcal A)$ and has the form (2.12)
-- statement:
--   Let $X$ be an affine process on $S_d^+$ with exponents $\varphi,\psi$, let $\chi$ be a truncation function, and let $(\alpha, b, \beta^{ij}, c, \gamma, m, \mu)$ be its parameters from Proposition 4.9: $\alpha, \beta^{ij}, c, \gamma, m, \mu$ satisfy the admissibility conditions of Definition 2.3, $b \in S_d^+$, and the right derivatives (2.2) of $\varphi,\psi$ at $t=0$ are given by (2.16)–(2.17).
--
--   Then the infinitesimal generator $\mathcal A$ of $X$ on $C_0(S_d^+)$ satisfies $\mathcal S_+ \subset D(\mathcal A)$, and for all $f \in \mathcal S_+$ and $x \in S_d^+$
--   $$\mathcal A f(x) = \mathcal A^\sharp f(x),$$
--   where $\mathcal A^\sharp$ is the right-hand side of (2.12) built from these parameters.
--
--   **Formalization Note.** $f \in \mathcal S_+$ is the restriction of a Schwartz function on $M_d$. "$f \in D(\mathcal A)$ and $\mathcal Af = \mathcal A^\sharp f$" means that $(P_t f - f)/t \to \mathcal A^\sharp f$ uniformly on $S_d^+$ as $t\downarrow 0$. The parameters are hypotheses (they are unique, so this is "for the parameters of $X$"). As a guard against Lean's convention that the integral of a non-integrable function is $0$, both integrands in (2.12) are also concluded integrable at every $x \in S_d^+$.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), Proposition 4.12, p. 29

import Mathlib
import Definitions.Def_AffinePSD_Necessity_Generator
import Definitions.Def_AffinePSD_Necessity_Process

open MeasureTheory ProbabilityTheory
open scoped SchwartzMap

namespace AffinePSD.Necessity

/-- Proposition 4.12 (arXiv:0910.0137v3, §4.2, p. 29): the infinitesimal generator `A` of an affine
process on `S_d^+` satisfies `S_+ ⊂ D(A)` and is of the form (2.12) for all `f ∈ S_+` and `x ∈ S_d^+`.

The parameters in (2.12) are those of Proposition 4.9: `α, β^{ij}, c, γ, m, μ` admissible, `b ∈ S_d^+`,
and `F`, `R` of (2.2) given by (2.16)–(2.17). They are taken as hypotheses (they are unique, so this is
"for the parameters of `X`").

**Formalization Note.** `f ∈ S_+` is `F|_{S_d^+}` for a Schwartz function `F` on `M_d`; "`f ∈ D(A)` and
`Af = A^♯ f`" is `HasGenerator` (uniform convergence of `(P_t f − f)/t` on `S_d^+`). Derivatives are the
symmetrized partials. Junk-integral guard: both integrands of (2.12) are concluded integrable. -/
theorem proposition_4_12 {d : ℕ} (χ : Trunc d) (p : ℝ → Kernel (Cone d) (Cone d))
    (φ : ℝ → Mat d → ℝ) (ψ : ℝ → Mat d → Mat d) (hX : IsAffineWith p φ ψ) (P : Params d)
    (hP : AdmissibleCore χ P) (hb : PSD P.b)
    (hFR : ∀ u : Mat d, PSD u →
      HasDerivWithinAt (fun t => φ t u) (Fpar P u) (Set.Ici 0) 0 ∧
      HasDerivWithinAt (fun t => ψ t u) (Rpar χ P u) (Set.Ici 0) 0) :
    ∀ F : 𝓢(Mat d, ℝ),
      HasGenerator p (fun x => F x) (Asharp χ P F) ∧
      ∀ x : Cone d,
        Integrable (fun ξ : Cone d => F ((x : Mat d) + (ξ : Mat d)) - F x) P.m ∧
        Integrable (fun ξ : Cone d => F ((x : Mat d) + (ξ : Mat d)) - F x -
          tr (χ.χ ξ) (grad F x)) (Mker P x) := by sorry

end AffinePSD.Necessity
