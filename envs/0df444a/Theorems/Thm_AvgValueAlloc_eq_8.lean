-- Prove2me | Theorems.Thm_AvgValueAlloc_eq_8
-- name    : AvgValueAlloc.eq_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:40:53.613866+00:00
-- url     : https://prove2.me/theorems/02aa5fff-dad8-4748-8d48-8af460c9e2bd
-- title:
--   (8): band bank count $(\sigma+1)^{k_\ell}$ and $\sum_\ell k_\ell c_\ell\le4P(M)$
-- statement:
--   Let $\rho\in\mathbb Q^n_{>0}$, $M$ funding items with ambiguity $\sigma_M$, $k_\ell$ the number of items of $M$ with a positive alternative in the dyadic band $I_\ell$, and $c_\ell=2^{\ell+1}$.
--
--   1. For every band $\ell$, the restrictions to $I_\ell$ of the banks $B(X)$ of all routings $X$ of $M$ take at most $(\sigma_M+1)^{k_\ell}$ values.
--   2. $$\sum_\ell k_\ell c_\ell\ \le\ 4P(M).\tag{8}$$
--
--   The count is the size of the union bound in Lemmas 3.1 and 3.2; (8) converts the resulting errors into units of $P(M)$.
--
--   Differences from the source:
--   - generalization: σ, an upper bound on the relevant positive ambiguity → σ_M, the ambiguity of M itself; reason: the least upper bound gives the bound for every larger σ, since (σ + 1)^{k_ℓ} increases with σ
--   - encoding: Σ over ℓ → Σ over the occupied bands; reason: k_ℓ = 0 for an empty band
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §3.1, p.7, eq. (8)

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_sigmaOn
import Definitions.Def_AvgValueAlloc_posVal
import Definitions.Def_AvgValueAlloc_routBank
import Definitions.Def_AvgValueAlloc_groupSum
import Definitions.Def_AvgValueAlloc_bandCount

namespace AvgValueAlloc

open scoped Classical in
/-- **(8): the band bank count and `Σ_ℓ k_ℓ c_ℓ ≤ 4P(M)`.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §3.1, p.7: "If k_ℓ items of M have an in-band positive
alternative, at most (σ + 1)^{k_ℓ} dyadic group banks are possible: each item contributes to one of
at most σ recipients or zero. With c_ℓ = 2^{ℓ+1}, Σ_ℓ k_ℓ c_ℓ ≤ 4P(M). (8)"

For thresholds `ρ > 0` and funding items `M` with ambiguity `σ_M`:
1. for every dyadic band `ℓ`, the set of restrictions to `I_ℓ` of the banks `B(X)` of all
   routings `X` of `M` has at most `(σ_M + 1)^{k_ℓ}` elements;
2. `Σ_ℓ k_ℓ 2^{ℓ+1} ≤ 4 P(M)`, the sum over the occupied bands.

**Formalization Note.** The bound is stated with `σ = σ_M`, the least upper bound on the relevant
ambiguity, which gives it for every larger `σ`. Bands with no buyer have `k_ℓ = 0`. -/
theorem eq_8 {n m : ℕ} (ρ : Fin n → ℚ) (hρ : ∀ j, 0 < ρ j) (M : Fin m → Vec n) :
    (∀ ℓ : ℤ,
      ((Finset.univ.filter (IsRouting ρ M)).image
          (fun X => fun j : {j : Fin n // dyBand ρ j = ℓ} => routBank ρ M X j.1)).card ≤
        (sigmaOn ρ (Finset.univ.image M) + 1) ^ bandCount ρ M ℓ) ∧
    ∑ ℓ ∈ Finset.univ.image (dyBand ρ), (bandCount ρ M ℓ : ℝ) * (2 : ℝ) ^ (ℓ + 1) ≤
      4 * posValSum ρ M := by sorry

end AvgValueAlloc
