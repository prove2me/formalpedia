-- Prove2me | Theorems.Thm_DedekindZeta_tsum_orbit_ofReal_norm_neg_re_ne_top
-- name    : DedekindZeta.tsum_orbit_ofReal_norm_neg_re_ne_top
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:46:06.830262+00:00
-- url     : https://prove2.me/theorems/cc930d48-58e1-41ee-8c2b-12a0bcbe907c
-- title:
--   Dedekind Zeta: tsum orbit of Real norm neg re ne top
-- statement:
--   **Finiteness of the orbit-indexed norm-power series** for the fractional cone
--   theta dominating series. For `1 < t.re`,
--   the `ℝ≥0∞`-valued series indexed by the `G`-orbits of the nonzero elements of `I`
--   (`G = Multiplicative (Fin (rank K) → ℤ)`, acting via `coneFracSMul`) of
--   `ofReal (N(σ a₀)^{-Re t})` for orbit representatives `a₀` is finite.
--
--   This is the genuine convergence threshold `Re t > 1`. Proof route:
--   clear denominators of `I` by `d : 𝓞 K`, `d ≠ 0` with `d • I ⊆ 𝓞 K`
--   (`FractionalIdeal.exists_eq_spanSingleton_mul`); for an orbit representative
--   `a₀ ∈ I`, `d·a₀ ∈ 𝓞 K` and by multiplicativity of the archimedean norm and the
--   norm bridge `N(σ b) = 𝔑((b))` (`mixedEmbedding_norm_eq_absNorm_span`, replicated
--   locally),
--   `N(σ a₀)^{-Re t} = |N d|^{Re t} · 𝔑((d·a₀))^{-Re t}`; the map
--   `o ↦ (d·a₀)` injects the orbit index (up to the finite torsion multiplicity
--   `w_K`) into `NonzeroIdeal K`, so the real series is summable by comparison with
--   the `Summable.of_norm` companion of `summable_absNorm_neg_cpow K (s := t) ht`,
--   and its `ENNReal.ofReal` tsum is `< ∞`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L2416-L2435
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L2416-L2435

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped NNReal ENNReal

theorem DedekindZeta.tsum_orbit_ofReal_norm_neg_re_ne_top
    (I : FractionalIdeal (𝓞 K)⁰ K) {t : ℂ} (ht : 1 < t.re) :
    (∑' o : Quotient (MulAction.orbitRel
          (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
          {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}),
        ENNReal.ofReal
          (mixedEmbedding.norm (mixedEmbedding K (Quotient.out o).1) ^ (-t.re)))
      ≠ ∞ := by sorry
