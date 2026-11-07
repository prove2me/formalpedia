-- Prove2me | Theorems.Thm_AvgValueAlloc_lemma_2_3
-- name    : AvgValueAlloc.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:40:03.082614+00:00
-- url     : https://prove2.me/theorems/5fb6a7b3-cfa5-432d-81ed-362b0a34bc97
-- title:
--   Lemma 2.3 — Physical realization, with the ledger invariant
-- statement:
--   Let $\rho\in\mathbb Q^n_{>0}$, $X$ a routing of funding items $M$ with welfare $W=W(X)$ and earned bank $B=B(X)$, and $Z$ fixed service contents of length $z$. Run the service kernel of §2.2 on $Z$ in uniform order: private ledgers start at $B$, physical surplus at any $C_0\ge B$; no negative proposal in the first $\lfloor z/2\rfloor$ positions; afterwards each occupied group proposes from a deterministic canonical optimum of its observed-prefix LP with edges of deficit above $B_j/8$ deleted, per-copy probabilities rounded down on a power-of-two grid with at least $100|J|z$ subdivisions; the physical winner is a maximum-original-value buyer among fitting private proposals and positive edges. Let $R$ be the original physical service welfare. Then:
--
--   1. with dyadic groups $I_\ell$: $\ W+G_Z(B)\le 80\,\mathbb E[W+R]$;
--   2. with shifted width-four groups $J_{\ell,s}$, $s\in\{0,1\}$: $\ W+G^s_Z(B)\le 160\,\mathbb E[W+R]$;
--   3. at every prefix, for every order and every proposal profile, $C_j\ge L_j\ge0$ for every buyer.
--
--   This is how a bank earned in funding is turned into actual prefix-feasible service welfare.
--
--   Differences from the source:
--   - generalization: a deterministic optimum, a grid with at least 100|J|z subdivisions, physical surplus with L_j = B_j ≤ C_j at service start → every canonical optimum chooser, every such grid, every initial physical surplus C₀ ≥ B; reason: the claims are asserted for the kernel whatever these choices are, and the page's kernel is one instance
--   - generalization: C_j ≥ L_j ≥ 0 at every prefix (of an actual run) → for every order and every proposal profile, including profiles of probability zero; reason: the invariant is deterministic (p.5: "The ledger invariant is deterministic"); it specializes to the realized runs
--   - encoding: the bank of the actual funding → B = B(X) for a routing X of welfare W; reason: the proof charges 8Σ_{B_j>0}ρ_j ≤ 8W to the routing that earned B; M, X, Z are arbitrary, so the bank may depend on the contents
--   - encoding: one maximum-original-value physical winner → least-index maximum; reason: the winner's value, hence R, is the same for every tie-break; proposals do not read winners
--   - encoding: aggregate equal types and divide by multiplicity → per-copy masses that are a function of the type and the prefix multiset; reason: aggregate mass = multiplicity × per-copy mass; same kernel
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §2.2, p.5 (kernel, invariant) and Lemma 2.3, p.5

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_welfare
import Definitions.Def_AvgValueAlloc_routBank
import Definitions.Def_AvgValueAlloc_groupSum
import Definitions.Def_AvgValueAlloc_IsSmallOptChooser
import Definitions.Def_AvgValueAlloc_svcRun
import Definitions.Def_AvgValueAlloc_expServiceR

namespace AvgValueAlloc

/-- **Lemma 2.3 (Physical realization), with the ledger invariant of §2.2.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §2.2, p.5: "Thus C_j ≥ L_j ≥ 0 at every prefix."; Lemma 2.3,
p.5: "For actual funding welfare W and fixed service contents in conditional uniform order,
original physical service welfare R satisfies W + G_Z(B) ≤ 80E[W + R]. For shifted width-four
groups, W + G^s_Z(B) ≤ 160E[W + R]. The bank may depend on the contents but not their order."

Let `ρ > 0`, `X` a routing of funding items `M` with welfare `W = W(X)` and earned bank
`B = B(X)`, `Z` service contents of length `z`, `opt` any deterministic canonical optimum chooser
of the small-edge prefix LPs (cutoff `B_j/8`), and physical surplus starting at `C₀ ≥ B`. Run the
service kernel of §2.2 on `Z` in uniform order, with rounding grids of at least `100|J|z`
subdivisions per group `J`. Then
1. with dyadic groups `I_ℓ`: `W + G_Z(B) ≤ 80 (W + E R)`;
2. with shifted width-four groups `J_{ℓ,s}`, `s ∈ {0,1}`: `W + G^s_Z(B) ≤ 160 (W + E R)`;
3. for every group partition, order, proposal profile and prefix, `0 ≤ L_j ≤ C_j` for every buyer.

**Formalization Note.** `B` is the bank of the actual routing `X`, as in the learner (the proof
charges `8 Σ_{B_j > 0} ρ_j ≤ 8W` to it); since `M`, `X` and `Z` are arbitrary, the bank may depend
on the contents. The invariant is stated for every proposal profile, not only those of positive
probability. -/
theorem lemma_2_3 {n m z : ℕ} (ρ : Fin n → ℚ) (hρ : ∀ j, 0 < ρ j) (M : Fin m → Vec n)
    (X : Fin m → Option (Fin n)) (hX : IsRouting ρ M X) (Z : Fin z → Vec n)
    (opt : Finset (Fin n) → Multiset (Vec n) → Vec n → Fin n → ℝ)
    (hopt : IsSmallOptChooser ρ (routBank ρ M X) opt) (C₀ : Fin n → ℝ)
    (hC₀ : routBank ρ M X ≤ C₀) :
    (∀ grid : ℤ → ℕ,
      (∀ g, 100 * (Finset.univ.filter fun j => dyBand ρ j = g).card * z ≤ 2 ^ grid g) →
        welfare M X + Gdy ρ Z (routBank ρ M X) ≤
          80 * (welfare M X + expServiceR ρ (dyBand ρ) opt grid (routBank ρ M X) C₀ Z)) ∧
    (∀ s : ℕ, s ≤ 1 → ∀ grid : ℤ → ℕ,
      (∀ g, 100 * (Finset.univ.filter fun j => shBand ρ s j = g).card * z ≤ 2 ^ grid g) →
        welfare M X + Gsh ρ s Z (routBank ρ M X) ≤
          160 * (welfare M X + expServiceR ρ (shBand ρ s) opt grid (routBank ρ M X) C₀ Z)) ∧
    (∀ (τ : Equiv.Perm (Fin z)) (prop : Fin z → Fin n → Bool) (a : ℕ), a ≤ z → ∀ j : Fin n,
      0 ≤ (svcRun ρ Z τ prop (routBank ρ M X) C₀ a).L j ∧
        (svcRun ρ Z τ prop (routBank ρ M X) C₀ a).L j ≤
          (svcRun ρ Z τ prop (routBank ρ M X) C₀ a).C j) := by sorry

end AvgValueAlloc
