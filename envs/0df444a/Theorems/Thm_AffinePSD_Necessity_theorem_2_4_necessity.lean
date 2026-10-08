-- Prove2me | Theorems.Thm_AffinePSD_Necessity_theorem_2_4_necessity
-- name    : AffinePSD.Necessity.theorem_2_4_necessity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:48:26.520994+00:00
-- url     : https://prove2.me/theorems/ce2b5417-368a-4455-a620-f9097b8d4c69
-- title:
--   Theorem 2.4 (first part) — affine processes on $S_d^+$ are regular and Feller, with generator (2.12) for an admissible parameter set
-- statement:
--   Let $X$ be an affine process on $S_d^+$ with transition family $p_t$ and exponents $\varphi, \psi$ in (2.1), and let $\chi$ be a truncation function. Then:
--
--   1. $X$ is regular and has the Feller property.
--   2. Let $\mathcal A$ be its infinitesimal generator on $C_0(S_d^+)$. Then $\mathcal S_+ \subset D(\mathcal A)$, and there is an admissible parameter set $(\alpha, b, \beta^{ij}, c, \gamma, m, \mu)$ (Definition 2.3, including $b \succeq (d-1)\alpha$) such that for $f \in \mathcal S_+$
--   $$\begin{aligned}\mathcal A f(x) ={}& \frac12 \sum_{i,j,k,l} A_{ijkl}(x)\, \frac{\partial^2 f(x)}{\partial x_{ij}\,\partial x_{kl}} + \sum_{i,j} \big(b_{ij} + B_{ij}(x)\big) \frac{\partial f(x)}{\partial x_{ij}} - \big(c + \langle \gamma, x\rangle\big) f(x) \\ &+ \int_{S_d^+\setminus\{0\}} \big(f(x+\xi) - f(x)\big)\, m(d\xi) + \int_{S_d^+\setminus\{0\}} \big(f(x+\xi) - f(x) - \langle \chi(\xi), \nabla f(x)\rangle\big)\, M(x,d\xi),\end{aligned} \qquad (2.12)$$
--   with $B$, $M$ and $A_{ijkl}$ as in (2.10), (2.8) and (2.13).
--   3. Moreover, for $u \in S_d^+$, $\varphi$ and $\psi$ solve the generalized Riccati equations
--   $$\frac{\partial \varphi(t,u)}{\partial t} = F(\psi(t,u)),\ \ \varphi(0,u) = 0, \qquad \frac{\partial\psi(t,u)}{\partial t} = R(\psi(t,u)),\ \ \psi(0,u) = u, \qquad (2.14),\ (2.15)$$
--   with $F$ and $R$ given by (2.16) and (2.17).
--
--   This is the necessity half of the characterization of affine processes on positive semidefinite matrices; the converse (existence and uniqueness for every admissible parameter set) is the subject of a separate mission.
--
--   **Formalization Note.** The transition family is indexed by $t\in\mathbb R$ and constrained at $t \ge 0$; the exponents are functions on $M_d$ used at positive semidefinite arguments. $\mathcal S_+$ is encoded by Schwartz functions on $M_d$ restricted to $S_d^+$; partial derivatives are taken in the symmetric directions $\tfrac12(E^{ij}+E^{ji})$. The generator statement is uniform convergence of $(P_tf - f)/t$ on $S_d^+$. The Feller property uses `EthierKurtz.IsStronglyContinuousContractionSemigroup`. $\mu$ is encoded by $(\nu, H)$ (see the parameter-set definition). The theorem holds for every truncation function, which is given first. As a guard against Lean's convention that the integral of a non-integrable function is $0$, the integrands of (2.12) and (2.16)–(2.17) are also concluded integrable.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), Theorem 2.4 (first part) and (2.12)–(2.17), pp. 9–10; proof in §6.1, p. 52

import Mathlib
import Definitions.Def_AffinePSD_Necessity_Generator
import Definitions.Def_AffinePSD_Necessity_Process

open MeasureTheory ProbabilityTheory
open scoped SchwartzMap

namespace AffinePSD.Necessity

/-- Theorem 2.4, first part (arXiv:0910.0137v3, §2, pp. 9–10). Suppose `X` is an affine process on
`S_d^+` (with exponents `φ, ψ` in (2.1)) and `χ` is a truncation function. Then `X` is regular and has
the Feller property; its generator `A` on `C_0(S_d^+)` satisfies `S_+ ⊂ D(A)`; and there is an admissible
parameter set `(α, b, β^{ij}, c, γ, m, μ)` (Definition 2.3, including (2.4)) such that `Af = A^♯ f` is
given by (2.12) for `f ∈ S_+`, and `φ, ψ` solve the generalized Riccati equations (2.14)–(2.15) with `F`,
`R` given by (2.16)–(2.17).

**Formalization Note.** Conventions: `M_d` as a Pi type with `⟨x,y⟩ = Tr(xy)`; `S_d^+` as a subtype;
`μ` encoded by `(ν, H)`; `S_+` by Schwartz functions on `M_d` restricted to `S_d^+`; symmetrized partial
derivatives; `HasGenerator` as uniform convergence on `S_d^+`; Feller via
`EthierKurtz.IsStronglyContinuousContractionSemigroup`; exponents on `M_d`, used at PSD arguments and
`t ≥ 0`. Junk-integral guard: the integrands of (2.12) and of (2.16)–(2.17) are concluded integrable. -/
theorem theorem_2_4_necessity {d : ℕ} (χ : Trunc d) (p : ℝ → Kernel (Cone d) (Cone d))
    (φ : ℝ → Mat d → ℝ) (ψ : ℝ → Mat d → Mat d) (hX : IsAffineWith p φ ψ) :
    IsRegular φ ψ ∧ IsFeller p ∧
    ∃ P : Params d, Admissible χ P ∧
      (∀ F : 𝓢(Mat d, ℝ),
        HasGenerator p (fun x => F x) (Asharp χ P F) ∧
        ∀ x : Cone d,
          Integrable (fun ξ : Cone d => F ((x : Mat d) + (ξ : Mat d)) - F x) P.m ∧
          Integrable (fun ξ : Cone d => F ((x : Mat d) + (ξ : Mat d)) - F x -
            tr (χ.χ ξ) (grad F x)) (Mker P x)) ∧
      SolvesRiccati (Fpar P) (Rpar χ P) φ ψ ∧
      ∀ u : Mat d, PSD u → IntegrableFR χ P u := by sorry

end AffinePSD.Necessity
