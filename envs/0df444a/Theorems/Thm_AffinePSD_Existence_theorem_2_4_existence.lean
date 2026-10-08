-- Prove2me | Theorems.Thm_AffinePSD_Existence_theorem_2_4_existence
-- name    : AffinePSD.Existence.theorem_2_4_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:54.860581+00:00
-- url     : https://prove2.me/theorems/775a8919-015a-4ade-a8fa-89bf82e8df3c
-- title:
--   Theorem 2.4 (second part) = Proposition 5.9 — every admissible parameter set gives a unique affine process on S_d^+ with generator (2.12)
-- statement:
--   Let $\chi$ be a truncation function and $(\alpha,b,\beta^{ij},c,\gamma,m,\mu)$ an admissible parameter set (Definition 2.3). Then there is an affine process on $S_d^+$, with transition family $(p_t)_{t\ge0}$ and exponents $\varphi,\psi$, such that:
--   1. its generator $\mathcal A$ on $C_0(S_d^+)$ contains every $f\in\mathcal S_+$ in its domain, and $\mathcal Af$ is given by (2.12);
--   2. for all $(t,u)\in\mathbb R_+\times S_d^+$ and $x\in S_d^+$,
--   $$\int_{S_d^+}e^{-\langle u,\xi\rangle}\,p_t(x,d\xi)=e^{-\varphi(t,u)-\langle\psi(t,u),x\rangle},$$
--   where $\varphi,\psi$ solve the generalized Riccati equations
--   $$\partial_t\varphi(t,u)=F(\psi(t,u)),\ \varphi(0,u)=0,\qquad\partial_t\psi(t,u)=R(\psi(t,u)),\ \psi(0,u)=u,$$
--   with $F,R$ from (2.16)–(2.17);
--   3. the process is unique: every affine transition family whose generator agrees with (2.12) on $\mathcal S_+$ coincides with $(p_t)$ for all $t\ge0$.
--
--   Moreover, the integrands of (2.12), (2.16) and (2.17) are integrable.
--
--   Together with the first part of Theorem 2.4 (every affine process has this form), this establishes a one-to-one correspondence between affine processes on $S_d^+$ and admissible parameter sets. That correspondence is what makes Wishart-type and matrix-valued stochastic-volatility models well defined.
--
--   **Formalization Note** The generator is the uniform limit of $(P_tf-f)/t$ on $S_d^+$, and $\mathcal S_+$ is represented by Schwartz functions on $M_d$. Uniqueness is stated for $t\ge0$, since values of the family at $t<0$ carry no meaning. "Given by (2.14) and (2.15)" is read as "a solution of": on $\partial S_d^+$, $R$ need not be Lipschitz, and the paper does not claim uniqueness there. The integrability conclusions rule out Lean's convention that a non-integrable integral is $0$.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), Theorem 2.4 (second part), p. 10; Proposition 5.9, p. 49; §6.1, p. 52

import Mathlib
import Definitions.Def_AffinePSD_Existence_Params
import Definitions.Def_AffinePSD_Necessity_Process
import Definitions.Def_AffinePSD_Existence_Generator

open MeasureTheory ProbabilityTheory
open scoped SchwartzMap

namespace AffinePSD.Existence

/-- Theorem 2.4, second part (arXiv:0910.0137v3, §2, p. 10), restated as Proposition 5.9
(§5.2, p. 49): for an admissible parameter set there is a unique affine process on `S_d^+` with
infinitesimal generator (2.12), and (2.1) holds for all `(t, u) ∈ R_+ × S_d^+` with `φ, ψ`
solving the generalized Riccati equations (2.14)–(2.15).
Formalization Note: existence is a transition family `p` that is affine with exponents `(φ, ψ)`,
whose generator on `C₀(S_d^+)` contains every `f ∈ S_+` (restrictions of Schwartz functions `F` on
`M_d`) with `A f` given by (2.12) (`HasGenerator`: uniform limit of `(P_t f − f)/t`), and with
`(φ, ψ)` solving (2.14)–(2.15) with `F, R` of (2.16)–(2.17). Uniqueness: any affine transition
family with the same generator on `S_+` agrees with `p` at every `t ≥ 0` (values at `t < 0` are
unconstrained, so `∃!` is not used). The conjuncts `GeneratorIntegrable` and `RiccatiIntegrable`
(the integrands of (2.12) and (2.16)–(2.17) are integrable) guard against Lean's junk value of a
non-integrable Bochner integral; they are consequences of admissibility, stronger than the page. -/
theorem theorem_2_4_existence {d : ℕ} (χ : AffinePSD.Necessity.Trunc d) (P : AffinePSD.Necessity.Params d) (hP : AffinePSD.Necessity.Admissible χ P) :
    ∃ (p : ℝ → Kernel (Cone d) (Cone d)) (φ : ℝ → Mat d → ℝ) (ψ : ℝ → Mat d → Mat d),
      GeneratorIntegrable χ P ∧ RiccatiIntegrable χ P ∧
      AffinePSD.Necessity.IsAffineWith p φ ψ ∧
      (∀ F : 𝓢(Mat d, ℝ), AffinePSD.Necessity.HasGenerator p (fun x => F x) (AffinePSD.Necessity.Asharp χ P F)) ∧
      AffinePSD.Necessity.SolvesRiccati (AffinePSD.Necessity.Fpar P) (AffinePSD.Necessity.Rpar χ P) φ ψ ∧
      ∀ p' : ℝ → Kernel (Cone d) (Cone d), AffinePSD.Necessity.IsAffine p' →
        (∀ F : 𝓢(Mat d, ℝ), AffinePSD.Necessity.HasGenerator p' (fun x => F x) (AffinePSD.Necessity.Asharp χ P F)) →
        ∀ t, 0 ≤ t → p' t = p t := by sorry

end AffinePSD.Existence
