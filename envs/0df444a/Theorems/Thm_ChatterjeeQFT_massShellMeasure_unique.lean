-- Prove2me | Theorems.Thm_ChatterjeeQFT_massShellMeasure_unique
-- name    : ChatterjeeQFT.massShellMeasure_unique
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:31:02.457327+00:00
-- url     : https://prove2.me/theorems/4ffc4493-775d-4d1a-97bf-deef31c042b2
-- title:
--   Uniqueness up to a constant of the Lorentz-invariant measure on $X_m$
-- statement:
--   Lecture 10 asserts that $\lambda_m$ is the *unique* measure on the mass shell, up to
--   a multiplicative constant, that is invariant under the restricted Lorentz group. Formally: let
--   $\mu$ be a Borel measure on $\mathbb{R}^{1,3}$ that is finite on compact sets, is carried by the
--   mass shell ($\mu(X_m^c) = 0$), and satisfies $L_{*}\mu = \mu$ for every
--   $L \in SO^{\uparrow}(1,3)$. Then $\mu = c\,\lambda_m$ for some constant $c \in [0,\infty]$.
--
--   The zero measure is allowed ($c = 0$), so the statement is the uniqueness of the invariant measure
--   up to scale, not its existence — existence is the content of the construction of $\lambda_m$
--   together with its invariance.
-- source:
--   S. Chatterjee, *Lectures on Quantum Field Theory* (Stanford, 2018-19, combined scribed lecture notes), https://souravchatterjee.su.domains/qft-lectures-combined.pdf, Lecture 10 §10.1, p. 41 ("$\lambda_m$ is the unique measure (up to a multiplicative constant) that is invariant under the action of the restricted Lorentz group on $X_m$").

import Mathlib
import Definitions.Def_ChatterjeeQFT_MassShell
open MeasureTheory Matrix
open scoped ENNReal

namespace ChatterjeeQFT

theorem massShellMeasure_unique (m : ℝ) (hm : 0 < m) (μ : Measure (Fin 4 → ℝ))
    [IsFiniteMeasureOnCompacts μ] (hμ : μ (massShell m)ᶜ = 0)
    (hinv : ∀ L : Matrix (Fin 4) (Fin 4) ℝ, IsRestrictedLorentz L →
      Measure.map (fun p : Fin 4 → ℝ => L *ᵥ p) μ = μ) :
    ∃ c : ℝ≥0∞, μ = c • massShellMeasure m := by sorry

end ChatterjeeQFT
