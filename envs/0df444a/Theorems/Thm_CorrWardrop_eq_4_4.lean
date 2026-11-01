-- Prove2me | Theorems.Thm_CorrWardrop_eq_4_4
-- name    : CorrWardrop.eq_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:28:22.298508+00:00
-- url     : https://prove2.me/theorems/1244f9be-9315-4d87-a22a-48f57dd61d7a
-- title:
--   (4.4), p.17 — $\Delta(\mathrm{WE}(\Gamma))\subseteq\mathrm{CWE}(\Gamma)\subseteq\mathrm{CCWE}(\Gamma)$ for every nonatomic game
-- statement:
--   Let $\Gamma=(\mathcal K,\gamma,\mathcal A,c)$ be a nonatomic game with flow set $\mathcal Y$. Then every distribution over Wardrop equilibria is a correlated Wardrop equilibrium, and every correlated Wardrop equilibrium is a coarse correlated Wardrop equilibrium:
--   $$
--   \Delta(\mathrm{WE}(\Gamma))\subseteq\mathrm{CWE}(\Gamma)\subseteq\mathrm{CCWE}(\Gamma).
--   $$
--   No potential is assumed. The first inclusion can be strict (El Farol, Example 1 of the paper); Proposition 4 shows that under a convex potential both inclusions are equalities.
--
--   Differences from the source:
--   - encoding: Δ(Y) Borel probability distributions on Y; Δ(WE(Γ)) distributions over WE → ProbabilityMeasure on the subtype Y; Δ(WE(Γ)) as the measures under which almost every flow is a WE; reason: WE(Γ) is closed, so the a.e. condition equals μ(WE(Γ)) = 1; same instances
-- source:
--   Koessler–Scarsini–Tomala, Correlated Equilibria in Large Anonymous Bayesian Games, arXiv:2107.06312v4, eq. (4.4), p.17

import Mathlib
import Definitions.Def_CorrWardrop_Model

open MeasureTheory

namespace CorrWardrop

/-- (4.4): for every nonatomic game, `Δ(WE(Γ)) ⊆ CWE(Γ) ⊆ CCWE(Γ)`.

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, (4.4), p.17. No potential is assumed. -/
theorem eq_4_4 {K : Type*} [Fintype K] {A : K → Type*} [∀ k, Fintype (A k)]
    (Γ : NonatomicGame K A) :
    DeltaWE Γ ⊆ CWE Γ ∧ CWE Γ ⊆ CCWE Γ := by sorry

end CorrWardrop
