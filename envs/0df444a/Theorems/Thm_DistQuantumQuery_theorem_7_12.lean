-- Prove2me | Theorems.Thm_DistQuantumQuery_theorem_7_12
-- name    : DistQuantumQuery.theorem_7_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:20:10.601287+00:00
-- url     : https://prove2.me/theorems/ff884df4-748f-4d0f-9160-502de5dda31f
-- title:
--   Theorem 7.12 — $Q^{\mu\circ(\nu_0,\nu_1)}_\varepsilon(f\circ g)=\Omega(Q^\mu_{\varepsilon'}(f)\,\mathrm{sfAdv}(g))$ and $\mathrm{sfAdv}(g)=\Theta(\lim_nQ_\varepsilon(\mathrm{TRIV}\circ g))$
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$, $f:\Sigma\to\Omega$ a functional problem and $\mu$ a distribution on $\Sigma$. Let $\Sigma_g\subseteq\{0,1\}^m$, $g:\Sigma_g\to\{0,1\}$ a decision problem and $\nu_0,\nu_1$ distributions supported on $g^{-1}(0)$ and $g^{-1}(1)$ (i.e. $\nu_b(x)\ne0\Rightarrow g(x)=b$). For constants $0<\varepsilon<\varepsilon'<1/2$,
--   $$
--   Q^{\mu\circ(\nu_0,\nu_1)}_\varepsilon(f\circ\mathbf g)=\Omega_{\varepsilon',\varepsilon}\Big(Q^\mu_{\varepsilon'}(f)\cdot\mathrm{sfAdv}^{(\nu_0,\nu_1)}(g)\Big).
--   $$
--   Moreover,
--   $$
--   \mathrm{sfAdv}^{(\nu_0,\nu_1)}(g)=\Theta_\varepsilon\Big(\lim_{n\to\infty}Q^{(\nu_0^{\otimes n}+\nu_1^{\otimes n})/2}_\varepsilon(\mathrm{TRIV}\circ\mathbf g)\Big).
--   $$
--   Precisely: (1) for all $0<\varepsilon<\varepsilon'<1/2$ there is $c>0$, depending only on $(\varepsilon,\varepsilon')$, such that $c\,Q^\mu_{\varepsilon'}(f)\,\mathrm{sfAdv}^{(\nu_0,\nu_1)}(g)\le Q^{\mu\circ(\nu_0,\nu_1)}_\varepsilon(f\circ\mathbf g)$ for every instance; (2) for every $\varepsilon\in(0,1/2)$ there are $c,C>0$, depending only on $\varepsilon$, such that for every $g,\nu_0,\nu_1$ the limit $L=\lim_nQ^{(\nu_0^{\otimes n}+\nu_1^{\otimes n})/2}_\varepsilon(\mathrm{TRIV}\circ\mathbf g)$ exists and $cL\le\mathrm{sfAdv}^{(\nu_0,\nu_1)}(g)\le CL$.
--
--   This is the first composition theorem for distributional quantum query complexity: the inner function contributes its Shaltiel-free adversary value, and this value is the right inner factor, since it equals (up to constants) the amortized cost of $\mathrm{TRIV}\circ\mathbf g$. Shaltiel's example shows that the naive product $Q^\mu(f)\cdot Q^\nu(g)$ fails.
--
--   **Formalization Note** All quantities are in $[0,\infty]$; $Q$ (in $\mathbb N\cup\{\infty\}$) is cast. The composed input is a bit string on $\iota\times\kappa$; the TRIV sequence is indexed by $n+1$ blocks.
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: min / max / inf of measures, +∞ if unbounded; Q an integer → values in ℝ≥0∞ (Q in ℕ∞, cast to ℝ≥0∞); min/inf as ⨅, max/sup as ⨆; reason: same values, with ⊤ for +∞; no real cast that would send ⊤ to 0
--   - encoding: index register with basis |0⟩,…,|n⟩ and an arbitrarily large ancilla → work register Option ι × Fin (d+1), none the null index, d existential; reason: the same oracle model; Fin (d+1) always contains the start vector
--   - reading: projective measurement: Π_s² = Π_s, Π_sΠ_t = 0, Σ_r Π_r = I (§2.3.2) → each Π_s also Hermitian; reason: the same paragraph reads outcome probabilities as Tr[Π_s ρ], which requires orthogonal projectors
--   - encoding: constants uniform over all instances → instances quantified with index and output types in Type (universe 0); reason: every instance of the source has finite index and output sets, which live in Type up to relabelling
--   - encoding: TRIV ∘ g with n blocks, n → ∞ → n + 1 blocks (Fin (n+1)); TRIV(x) = [x = 1^n]; reason: TRIV on zero bits is undefined; shifting the index does not change limits; [x = 1^n] equals b on b^n for n ≥ 1
--   - reading: “For constants 0 < ε < ε′ < 1/2 … Ω_{ε′,ε}(·) … Moreover … Θ_ε(·)” → (1) ∀ 0 < ε < ε′ < 1/2, ∃ c > 0 before every instance; (2) ∀ ε ∈ (0, 1/2), ∃ c, C > 0 before g, ν₀, ν₁ (and n); reason: the subscripts name the only dependence of the hidden constants; the range of ε in the “Moreover” is inherited from the theorem's sentence (informal Theorem 1.1 says “any ε > 0”; the formal Theorem 7.12 governs)
--   - encoding: the limit lim_{n→∞} Q(...) as a real number → ∃ L ∈ ℝ≥0∞ with Tendsto (Q_n) atTop (𝓝 L); reason: existence of the limit is part of the conclusion; the sequence is ℕ-valued
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Theorem 7.12, p.67

import Mathlib
import Definitions.Def_DistQuantumQuery_Qdist
import Definitions.Def_DistQuantumQuery_sfAdv
import Definitions.Def_DistQuantumQuery_compose

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Theorem 7.12** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Theorem 7.12, p.67). Let `Σ ⊆ {0,1}^n`, `f : Σ → Ω` a functional problem
and `μ` a distribution on `Σ`. Let `Σ_g ⊆ {0,1}^m`, `g : Σ_g → {0,1}` a decision problem and `ν₀, ν₁`
distributions supported on `g⁻¹(0)`, `g⁻¹(1)`. For constants `0 < ε < ε′ < 1/2`,
`Q^{μ∘(ν₀,ν₁)}_ε(f ∘ g) = Ω_{ε′,ε}(Q^μ_{ε′}(f) · sfAdv^{(ν₀,ν₁)}(g))`.
Moreover,
`sfAdv^{(ν₀,ν₁)}(g) = Θ_ε(lim_{n→∞} Q^{(ν₀^{⊗n}+ν₁^{⊗n})/2}_ε(TRIV ∘ g))`.

**Formalization Note** (1) For all `0 < ε < ε′ < 1/2` there is `c > 0`, depending only on
`(ε, ε′)` and chosen before every instance (positions `ι`, `κ`, output set `Ω`, `Σ`, `f`, `μ`, `Σ_g`,
`g`, `ν₀`, `ν₁`), with `c · Q^μ_{ε′}(f) · sfAdv(g) ≤ Q^η_ε(f ∘ g)`, `η = μ ∘ (ν₀, ν₁)`.
(2) For every `ε ∈ (0, 1/2)` there are `c, C > 0`, depending only on `ε`, such that for every
`g, ν₀, ν₁` the limit `L` of `Q^{μ_n}_ε(TRIV ∘ g)` exists (in `ℝ≥0∞`) and `c·L ≤ sfAdv(g) ≤ C·L`. The
sequence is indexed by `n + 1` blocks. Everything is in `ℝ≥0∞`; `Q` (in `ℕ∞`) is cast. Index and
output types range over `Type`. Functional problems enter `Q` as `graphRel`. -/
theorem theorem_7_12 :
    (∀ ε ε' : ℝ, 0 < ε → ε < ε' → ε' < 1 / 2 → ∃ c : ℝ, 0 < c ∧
      ∀ (ι κ Ω : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype Ω]
        [DecidableEq Ω] (S : Finset (ι → Bool)) (f : S → Ω) (μ : S → ℝ)
        (Sg : Finset (κ → Bool)) (g : Sg → Bool) (ν₀ ν₁ : Sg → ℝ),
        IsDist μ → IsDist ν₀ → IsDist ν₁ → (∀ x, ν₀ x ≠ 0 → g x = false) →
        (∀ x, ν₁ x ≠ 0 → g x = true) →
        ENNReal.ofReal c * (Qdist S μ (graphRel f) ε' : ℝ≥0∞) * sfAdv Sg g ν₀ ν₁ ≤
          (Qdist (compDomain S Sg g) (compDist g μ ν₀ ν₁) (graphRel (compose f g)) ε : ℝ≥0∞)) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (Sg : Finset (κ → Bool)) (g : Sg → Bool)
        (ν₀ ν₁ : Sg → ℝ),
        IsDist ν₀ → IsDist ν₁ → (∀ x, ν₀ x ≠ 0 → g x = false) → (∀ x, ν₁ x ≠ 0 → g x = true) →
        ∃ L : ℝ≥0∞,
          Filter.Tendsto
            (fun n : ℕ => (Qdist (trivDomain n Sg g) (trivDist n ν₀ ν₁)
              (graphRel (trivComp n g)) ε : ℝ≥0∞))
            Filter.atTop (𝓝 L) ∧
          ENNReal.ofReal c * L ≤ sfAdv Sg g ν₀ ν₁ ∧ sfAdv Sg g ν₀ ν₁ ≤ ENNReal.ofReal C * L) := by sorry

end DistQuantumQuery
