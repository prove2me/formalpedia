-- Prove2me | Theorems.Thm_DistQuantumQuery_lemma_6_11
-- name    : DistQuantumQuery.lemma_6_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:19:40.600045+00:00
-- url     : https://prove2.me/theorems/e55bf538-a086-4bb0-963d-e1f8a51f40b7
-- title:
--   Lemma 6.11 — $\delta\mapsto\mathrm{rAdv}^\nu_\delta(g)/(1-\delta)$ is non-increasing
-- statement:
--   Let $g:\Sigma\to\{0,1\}$ be a decision problem on $\Sigma\subseteq\{0,1\}^m$, $\nu_0,\nu_1$ distributions supported on $g^{-1}(0)$ and $g^{-1}(1)$ (i.e. $\nu_b(x)\ne0\Rightarrow g(x)=b$), and $\nu=(\nu_0+\nu_1)/2$. Then for every $0\le\alpha<\beta<1$,
--   $$
--   \frac{\mathrm{rAdv}^\nu_\alpha(g)}{1-\alpha}\ \ge\ \frac{\mathrm{rAdv}^\nu_\beta(g)}{1-\beta}.
--   $$
--   So the infimum defining $\mathrm{sfAdv}$ is approached as $\delta\to1$.
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: min / max / inf of measures, +∞ if unbounded; Q an integer → values in ℝ≥0∞ (Q in ℕ∞, cast to ℝ≥0∞); min/inf as ⨅, max/sup as ⨆; reason: same values, with ⊤ for +∞; no real cast that would send ⊤ to 0
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Lemma 6.11, p.53

import Mathlib
import Definitions.Def_DistQuantumQuery_sfAdv

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Lemma 6.11** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Lemma 6.11, p.53). Let `g : Σ → {0,1}` be a decision problem on
`Σ ⊆ {0,1}^m`, `ν₀, ν₁` distributions supported on `g⁻¹(0)`, `g⁻¹(1)`, and `ν = (ν₀ + ν₁)/2`. Then for
every `0 ≤ α < β < 1`, `rAdv^ν_α(g)/(1 − α) ≥ rAdv^ν_β(g)/(1 − β)`.

**Formalization Note** Values in `ℝ≥0∞`. -/
theorem lemma_6_11 {κ : Type*} [Fintype κ] [DecidableEq κ] (Sg : Finset (κ → Bool))
    (g : Sg → Bool) (ν₀ ν₁ : Sg → ℝ) (hν₀ : IsDist ν₀) (hν₁ : IsDist ν₁)
    (hs₀ : ∀ x, ν₀ x ≠ 0 → g x = false) (hs₁ : ∀ x, ν₁ x ≠ 0 → g x = true) (α β : ℝ) (hα : 0 ≤ α) (hαβ : α < β) (hβ : β < 1) :
    rAdv Sg (fun x => (ν₀ x + ν₁ x) / 2) g β / ENNReal.ofReal (1 - β) ≤
      rAdv Sg (fun x => (ν₀ x + ν₁ x) / 2) g α / ENNReal.ofReal (1 - α) := by sorry

end DistQuantumQuery
