-- Prove2me | Theorems.Thm_DistQuantumQuery_proposition_7_10
-- name    : DistQuantumQuery.proposition_7_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:19:51.613962+00:00
-- url     : https://prove2.me/theorems/59332128-159c-4e5c-92ab-b0fd6a0fb6f0
-- title:
--   Proposition 7.10 — $\mathrm{sfAdv}^{(\nu_0,\nu_1)}(g)=\lim_n\mathrm{rAdv}^{(\nu_0^{\otimes n}+\nu_1^{\otimes n})/2}_\varepsilon(\mathrm{TRIV}\circ\mathbf g)/(1-\varepsilon)$
-- statement:
--   Let $g:\Sigma_g\to\{0,1\}$ be a decision problem on $\Sigma_g\subseteq\{0,1\}^m$ and $\nu_0,\nu_1$ distributions supported on $g^{-1}(0)$ and $g^{-1}(1)$ (i.e. $\nu_b(x)\ne0\Rightarrow g(x)=b$). Then for any fixed $\varepsilon\in(0,1)$,
--   $$
--   \mathrm{sfAdv}^{(\nu_0,\nu_1)}(g)=\lim_{n\to\infty}\frac{\mathrm{rAdv}^{(\nu_0^{\otimes n}+\nu_1^{\otimes n})/2}_\varepsilon(\mathrm{TRIV}\circ\mathbf g)}{1-\varepsilon}.
--   $$
--   The Shaltiel-free measure is thus exactly the amortized relaxed-adversary cost of deciding $g$ on many correlated copies; this is the third item of Theorem 7.1.
--
--   **Formalization Note** The statement asserts that the limit exists and equals $\mathrm{sfAdv}$.
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: min / max / inf of measures, +∞ if unbounded; Q an integer → values in ℝ≥0∞ (Q in ℕ∞, cast to ℝ≥0∞); min/inf as ⨅, max/sup as ⨆; reason: same values, with ⊤ for +∞; no real cast that would send ⊤ to 0
--   - encoding: TRIV ∘ g with n blocks, n → ∞ → n + 1 blocks (Fin (n+1)); TRIV(x) = [x = 1^n]; reason: TRIV on zero bits is undefined; shifting the index does not change limits; [x = 1^n] equals b on b^n for n ≥ 1
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Proposition 7.10, p.64; Theorem 7.1, p.55

import Mathlib
import Definitions.Def_DistQuantumQuery_sfAdv
import Definitions.Def_DistQuantumQuery_compose

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Proposition 7.10** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Proposition 7.10, p.64). Let `g : Σ_g → {0,1}` be a decision
problem on `Σ_g ⊆ {0,1}^m` and `ν₀, ν₁` distributions supported on `g⁻¹(0)`, `g⁻¹(1)`. Then for any
fixed `ε ∈ (0,1)`,
`sfAdv^{(ν₀,ν₁)}(g) = lim_{n→∞} rAdv^{(ν₀^{⊗n}+ν₁^{⊗n})/2}_ε(TRIV ∘ g) / (1 − ε)`.

**Formalization Note** The limit exists and equals `sfAdv` (`Tendsto`, in `ℝ≥0∞`). The sequence
is indexed by `n + 1` blocks (`trivDomain n`); `(ν₀^{⊗n}+ν₁^{⊗n})/2` is `trivDist n`. -/
theorem proposition_7_10 {κ : Type*} [Fintype κ] [DecidableEq κ] (Sg : Finset (κ → Bool))
    (g : Sg → Bool) (ν₀ ν₁ : Sg → ℝ) (hν₀ : IsDist ν₀) (hν₁ : IsDist ν₁)
    (hs₀ : ∀ x, ν₀ x ≠ 0 → g x = false) (hs₁ : ∀ x, ν₁ x ≠ 0 → g x = true) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    Filter.Tendsto
      (fun n : ℕ => rAdv (trivDomain n Sg g) (trivDist n ν₀ ν₁) (trivComp n g) ε /
        ENNReal.ofReal (1 - ε))
      Filter.atTop (𝓝 (sfAdv Sg g ν₀ ν₁)) := by sorry

end DistQuantumQuery
