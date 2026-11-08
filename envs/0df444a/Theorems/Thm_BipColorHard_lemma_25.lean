-- Prove2me | Theorems.Thm_BipColorHard_lemma_25
-- name    : BipColorHard.lemma_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:36:36.762738+00:00
-- url     : https://prove2.me/theorems/a3fd2abd-7a94-4b6f-a656-11f9810126b3
-- title:
--   Lemma 25 — a fixed base graph with the two-orientation mixture $\xi_m$
-- statement:
--   Let $q=2k+1\ge3$ with $D$ as above, and let $P_S,R_S$ be the phases of Lemma 28. For every integer $m\ge1$ and $\zeta>0$, there is a finite simple bipartite graph $\Gamma$ from the family of §6.2, with $m$ distinct ordered open vertices of degree $D-1$ on each side and every other vertex of degree $D$, such that
--   $$e^{-\zeta}\xi_m(\tau,\tau')\le\mu_\Gamma(\tau,\tau')\le e^{\zeta}\xi_m(\tau,\tau')\qquad(\tau,\tau'\in[q]^m).$$
--
--   This is the base of the gadget of Lemma 13: the open vertices of $\Gamma$ are colored almost as in an equal mixture of the $2Q$ phases.
--
--   Differences from the source:
--   - encoding: the phases $P_S,R_S$ of Lemma 28 → $\exists$ `Pf Rf` with `IsPhaseFamily`, the specification that determines them uniquely; reason: the existential cannot be vacuous, unlike a universal over the phases
--   - encoding: a graph in the family, with the stated degrees → a simple point of `BaseMatchings`, with $m<n$; reason: the degrees follow from the matchings and simplicity
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), Lemma 25, p.28 (PDF p.30)

import Definitions.Def_BipColorHard_Hardness
import Definitions.Def_BipColorHard_RandomGraph

set_option autoImplicit false

namespace BipColorHard

/-- **Lemma 25**, p.28 (PDF p.30), manuscript sha256 78a66d1f…, for `q = 2k + 1 ≥ 3`, `D` of §3. With `P_S`, `R_S` the phases of
Lemma 28: for every integer `m ≥ 1` and `ζ > 0`, there is a finite simple bipartite graph `Γ` from the family of §6.2, with `m`
distinct ordered open vertices of degree `D - 1` on each side and every other vertex of degree `D`, such that
`e^{-ζ} ξ_m(τ, τ') ≤ μ_Γ(τ, τ') ≤ e^{ζ} ξ_m(τ, τ')` for all `τ, τ' ∈ [q]^m`.

**Formalization Note.** The phases are quantified existentially together with their specification `IsPhaseFamily`, which pins
them down uniquely. A point `M` of the model has the stated degrees automatically once it is simple. -/
theorem lemma_25 (k : ℕ) (hk : 1 ≤ k) :
    ∃ Pf Rf : Omega k → Fin (2 * k + 1) → ℝ,
      IsPhaseFamily (expP (bipDeg (2 * k + 1))) Pf Rf ∧
      ∀ (m : ℕ), 1 ≤ m → ∀ ζ : ℝ, 0 < ζ →
        ∃ (n : ℕ) (M : BaseMatchings (bipDeg (2 * k + 1)) n m), m < n ∧ M.IsSimple ∧
          ∀ τ τ' : Fin m → Fin (2 * k + 1),
            Real.exp (-ζ) * xiM Pf Rf τ τ' ≤ muGamma M τ τ' ∧
              muGamma M τ τ' ≤ Real.exp ζ * xiM Pf Rf τ τ' := by sorry

end BipColorHard
