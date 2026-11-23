-- Prove2me | Theorems.Thm_DedekindZeta_summable_orbit_norm_neg_re
-- name    : DedekindZeta.summable_orbit_norm_neg_re
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:46:09.33365+00:00
-- url     : https://prove2.me/theorems/e34c0497-885f-4fe8-836f-c3293ed11a89
-- title:
--   Dedekind Zeta: summable orbit norm neg re
-- statement:
--   **Summability of the orbit-indexed real norm-power family** (the genuine
--   `1 < Re t` convergence input for the fractional cone theta dominating series).
--   For `1 < t.re`, the nonnegative real family indexed by the `G`-orbits of the
--   nonzero elements of `I` (`G = Multiplicative (Fin (rank K) → ℤ)`, acting via
--   `coneFracSMul`) of `N(σ a₀)^{-Re t}` for orbit representatives `a₀` is summable.
--
--   Proof route: clear denominators of `I` via `d := (I.den : 𝓞 K)`
--   (`FractionalIdeal.den_mul_self_eq_num`), so for an orbit representative
--   `a₀ = (Quotient.out o).1 ∈ I` there is `b₀ : 𝓞 K`, `b₀ ≠ 0`, with
--   `(b₀ : K) = (d : K) * a₀`; by `mixedEmbedding.norm_eq_norm`, multiplicativity of
--   `Algebra.norm`, and the norm bridge `N(σ b) = 𝔑((b))`
--   (`mixedEmbedding_norm_eq_absNorm_span`, replicated locally),
--   `N(σ a₀)^{-Re t} = |N d|^{Re t} · 𝔑((b₀))^{-Re t}`. The map `o ↦ Ideal.span {b₀}`
--   sends the orbit index into `NonzeroIdeal K` with multiplicity bounded by the
--   finite torsion order `w_K = Units.torsionOrder K` (two reps generating the same
--   principal ideal differ by a unit, hence by a torsion factor modulo the free part
--   `coneUnitHom`; `coneUnitHom_mem_torsion_iff`). Comparison with the real family
--   `𝔑^{-Re t}` — summable as `summable_norm_iff.mpr (summable_absNorm_neg_cpow K
--   (s := t) ht)`, using `‖𝔑^{-t}‖ = 𝔑^{-Re t}` — then gives summability.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L2371-L2397
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L2371-L2397

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
set_option maxHeartbeats 1000000

theorem DedekindZeta.summable_orbit_norm_neg_re
    (I : FractionalIdeal (𝓞 K)⁰ K) {t : ℂ} (ht : 1 < t.re) :
    Summable (fun o : Quotient (MulAction.orbitRel
          (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
          {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}) =>
        mixedEmbedding.norm (mixedEmbedding K (Quotient.out o).1) ^ (-t.re)) := by sorry
