-- Prove2me | Theorems.Thm_BalkemaDeHaan_ExpDomain_max_to_residual
-- name    : BalkemaDeHaan.ExpDomain.max_to_residual
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:25.366984+00:00
-- url     : https://prove2.me/theorems/dbeb5632-9e9c-4b56-acf4-6f58d07dd216
-- title:
--   Proof of Theorem 3 — D(Λ) ∩ D₀ is contained in D_r(Π)
-- statement:
--   If the normalized maxima of a distribution $F$ converge weakly to the Gumbel law $\Lambda$ and $R(x)=1-F(x)>0$ for every real $x$, then the normalized residual-life distributions converge weakly to the exponential law $\Pi$ for suitable positive scales and shifts. In symbols,
--
--   $$D(\Lambda)\cap D_0\subseteq D_r(\Pi).$$
--
--   This is the forward construction in the proof of Theorem 3. The assumption $D_0$ keeps every residual-life conditional distribution defined.
--
--   **Formalization Note** The $D_r$ shift acts on $X-t$ as specified in §2; the proof's tail quotient uses an equivalent shift of $X$ after adding $t$.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), pp. 798–799 (PDF 7–8), proof of Theorem 3

import Definitions.Def_BalkemaDeHaan_ExpDomain_Domains

namespace BalkemaDeHaan.ExpDomain

open MeasureTheory

/-- The `D(Λ) ∩ D₀ ⊆ D_r(Π)` half of Theorem 3, pp. 798–799. -/
theorem max_to_residual (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmax : InD μ lambdaLaw) (hpositive : InDZero μ) :
    InDr μ piLaw := by sorry

end BalkemaDeHaan.ExpDomain
