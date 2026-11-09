-- Prove2me | Theorems.Thm_AgnosticTNS_corollary_2_7
-- name    : AgnosticTNS.corollary_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:34:34.379957+00:00
-- url     : https://prove2.me/theorems/b78a3a41-9d0e-429d-ba8c-fc6f87f1cd09
-- title:
--   Corollary 2.7 — subnormalised tomography from success-probability bounds (corrected: $1+\log(1/\delta)$ in (2.15))
-- statement:
--   Let $K$ be a known postselection map ($K^\dagger K\le I$) on $n$ qudits, $A\subseteq[n]$ and $D_A=d^{|A|}$. Write $\mu_K(\rho)=\mathrm{tr}(K\rho K^\dagger)$ and $\sigma_{K,A}(\rho)=\mathrm{tr}_{[n]\setminus A}(K\rho K^\dagger)$. Let $m_A$ be the copy function of a normalised tomography procedure. Suppose $\rho_{K,A}=\sigma_{K,A}(\rho)/\mu_K(\rho)$ has rank at most $r$ and known bounds $0<\mu_\ell\le\mu_K(\rho)\le\mu_u\le1$ hold.
--
--   1. If $\mu_u\le\eta$, the zero operator satisfies $\|\sigma_{K,A}(\rho)-0\|_1\le\eta$.
--   2. Otherwise let $N=m_A(r,D_A,\eta/(2\mu_u),\delta/3)$ and
--   $$
--   m_B=\left\lceil\frac{2N}{\mu_\ell}+\frac{8}{\mu_\ell}\log\frac3\delta+\frac2{\eta^2}\log\frac6\delta\right\rceil .
--   $$
--   There is a measurement on $m_B$ copies of $\rho$ which records which copies pass the postselection, returns a failure flag whenever fewer than $N$ copies pass, and otherwise returns a positive semidefinite estimate $\hat\sigma_A$ of trace at most one; for every $\rho$ as above it returns $\hat\sigma_A$ with
--   $$
--   \|\sigma_{K,A}(\rho)-\hat\sigma_A\|_1\le\eta
--   $$
--   with probability at least $1-\delta$.
--   3. If $m_A(r,D,\eta,\beta)\le C(rD+\log(1/\beta))/\eta^2$ as in (2.11), then
--   $$
--   m_B\le C'\left(\frac{\mu_u^2\,(rD_A+1+\log(1/\delta))}{\mu_\ell\,\eta^2}+\frac{1+\log(1/\delta)}{\mu_\ell}+\frac{1+\log(1/\delta)}{\eta^2}\right)
--   $$
--   for a constant $C'$ depending only on $C$.
--
--   This turns normalised tomography into tomography of the subnormalised states produced by postselection, counting every input copy.
--
--   Differences from the source:
--   - encoding: standing assumptions $n\ge1$, $d\ge2$, $\epsilon\in(0,1]$, $\delta\in(0,1)$ of p.11 → explicit hypotheses; reason: the section's standing assumptions are binders
--   - generalization: the normalised tomography algorithm of [Pel+25, Theorem 1.3] with copy function $m_A$ → every normalised tomography procedure with copy function $m_A$ (`NormTomography`); reason: the proof uses only the procedure's guarantee; [Pel+25] is such a procedure, so the statement specialises to the source's
--   - encoding: a procedure using at most $m_B$ original copies that returns a failure flag if fewer than $N$ copies pass → a finite-outcome POVM on exactly $m_B=\lceil(2.14)\rceil$ copies whose coarse-graining is the per-copy postselection measurement $\{K^\dagger K,I-K^\dagger K\}$, with estimate `none` whenever fewer than $N$ copies pass; reason: measurement model of a procedure on copies; a copy count is an integer and unused copies can be ignored
--   - encoding: $\operatorname{rank}\rho_{K,A}\le r$ → $\operatorname{rank}\sigma_{K,A}(\rho)\le r$; reason: $\rho_{K,A}=\sigma_{K,A}(\rho)/\mu_K(\rho)$ with $\mu_K(\rho)>0$ has the same rank
--   - reading: "With (2.11), the copy bound is $O(\cdot)$" → for every constant $C$ in (2.11) there is $C'$ depending only on $C$; reason: the hidden constant of (2.15) can only depend on the constant of (2.11)
--   - correction: $\log(1/\delta)$ in the three terms of (2.15) → $1+\log(1/\delta)$; reason: the printed bound fails as $\delta\to1$: with $\mu_\ell=\mu_u=\mu$, $\eta=\mu/2$, $rD_A=1$, (2.14) gives $m_B\ge(2/\eta^2)\log6=8\log6/\mu^2$ while the printed bracket tends to $4/\mu$, so no constant works as $\mu\to0$
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Corollary 2.7, Eqs. (2.12)–(2.15), pp.14–15

import Mathlib
import Definitions.Def_AgnosticTNS_NormTomography
import Definitions.Def_AgnosticTNS_ptrace
open Matrix
open scoped ComplexOrder
open Classical

namespace AgnosticTNS

/-- **Corollary 2.7 (Subnormalised tomography from bounds on success probability)**, pp.14–15
(Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). Let `K` be a known postselection map (`K†K ≤ I`), `A ⊆ [n]`, `D_A = d^{|A|}`, and suppose
`ρ_{K,A}` has rank at most `r` and known bounds `0 < µ_ℓ ≤ µ_K(ρ) ≤ µ_u ≤ 1` (2.12) hold, where
`µ_K(ρ) = tr(KρK†)` and `σ_{K,A}(ρ) = tr_{[n]∖A}(KρK†)`.
1. If `µ_u ≤ η`, the zero operator satisfies `‖σ_{K,A}(ρ) − 0‖₁ ≤ η`.
2. Otherwise, with `N = m_A(r, D_A, η/(2µ_u), δ/3)` and
   `m_B = ⌈2N/µ_ℓ + (8/µ_ℓ) log(3/δ) + (2/η²) log(6/δ)⌉` (2.14), there is a measurement on `m_B`
   original copies which first records which copies pass the postselection, returns a failure flag
   when fewer than `N` copies pass, otherwise a positive semidefinite estimate `σ̂_A` of trace at most
   one, and with probability at least `1 − δ` returns `σ̂_A` with `‖σ_{K,A}(ρ) − σ̂_A‖₁ ≤ η` (2.13).
3. (2.15) If `m_A(r, D, η, β) ≤ C (rD + log(1/β))/η²` (2.11), then
   `m_B ≤ C' (µ_u²(rD_A + 1 + log(1/δ))/(µ_ℓη²) + (1 + log(1/δ))/µ_ℓ + (1 + log(1/δ))/η²)` with `C'`
   depending only on `C`.

**Formalization Note** The paper fixes the procedure of [Pel+25]; here `m_A` is the copy function of
any normalised tomography procedure (`NormTomography`). In (2.15) `log(1/δ)` is `1 + log(1/δ)`: the
printed bound fails as `δ → 1` (see the item's Differences list). The measurement on `m_B` copies is a
finite-outcome POVM whose coarse-graining is the per-copy postselection measurement. -/
theorem corollary_2_7 :
    (∀ {n d : ℕ}, 1 ≤ n → 2 ≤ d → ∀ mA : ℕ → ℕ → ℝ → ℝ → ℕ, NormTomography mA →
      ∀ (K : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ), (1 - Kᴴ * K).PosSemidef →
      ∀ (A : Finset (Fin n)) (r : ℕ) (μl μu η δ : ℝ), 1 ≤ r → 0 < μl → μl ≤ μu → μu ≤ 1 → 0 < η →
        0 < δ → δ < 1 →
        (μu ≤ η → ∀ ρ, WildeQIT.IsDensityOperator ρ → μl ≤ (K * ρ * Kᴴ).trace.re →
          (K * ρ * Kᴴ).trace.re ≤ μu → WildeQIT.traceNorm (ptrace A (K * ρ * Kᴴ) - 0) ≤ η) ∧
        (η < μu →
          ∃ (Ω : Type) (_ : Fintype Ω)
            (E : (Fin ⌈2 * (mA r (d ^ A.card) (η / (2 * μu)) (δ / 3) : ℝ) / μl +
                    8 / μl * Real.log (3 / δ) + 2 / η ^ 2 * Real.log (6 / δ)⌉₊ → Bool) × Ω →
              Matrix (Fin ⌈2 * (mA r (d ^ A.card) (η / (2 * μu)) (δ / 3) : ℝ) / μl +
                    8 / μl * Real.log (3 / δ) + 2 / η ^ 2 * Real.log (6 / δ)⌉₊ → Fin n → Fin d)
                (Fin ⌈2 * (mA r (d ^ A.card) (η / (2 * μu)) (δ / 3) : ℝ) / μl +
                    8 / μl * Real.log (3 / δ) + 2 / η ^ 2 * Real.log (6 / δ)⌉₊ → Fin n → Fin d) ℂ)
            (est : (Fin ⌈2 * (mA r (d ^ A.card) (η / (2 * μu)) (δ / 3) : ℝ) / μl +
                    8 / μl * Real.log (3 / δ) + 2 / η ^ 2 * Real.log (6 / δ)⌉₊ → Bool) × Ω →
              Option (Matrix (↥A → Fin d) (↥A → Fin d) ℂ)),
            (∀ ω, (E ω).PosSemidef) ∧ ∑ ω, E ω = 1 ∧
            (∀ b, ∑ ω', E (b, ω') =
              Matrix.of fun x y => ∏ k, (if b k then Kᴴ * K else 1 - Kᴴ * K) (x k) (y k)) ∧
            (∀ b ω', (Finset.univ.filter fun k => b k = true).card <
              mA r (d ^ A.card) (η / (2 * μu)) (δ / 3) → est (b, ω') = none) ∧
            (∀ ω M, est ω = some M → M.PosSemidef ∧ M.trace.re ≤ 1) ∧
            ∀ ρ, WildeQIT.IsDensityOperator ρ → μl ≤ (K * ρ * Kᴴ).trace.re →
              (K * ρ * Kᴴ).trace.re ≤ μu → (ptrace A (K * ρ * Kᴴ)).rank ≤ r →
              1 - δ ≤ ∑ ω, if ∃ M, est ω = some M ∧ WildeQIT.traceNorm (ptrace A (K * ρ * Kᴴ) - M) ≤ η
                then (E ω * ShadowTomography.UpperBound.tensorPow ρ _).trace.re else 0)) ∧
    ∀ C : ℝ, 0 < C → ∃ C' : ℝ, 0 < C' ∧ ∀ mA : ℕ → ℕ → ℝ → ℝ → ℕ,
      (∀ r D η β, 1 ≤ r → 1 ≤ D → 0 < η → 0 < β → β < 1 →
        (mA r D η β : ℝ) ≤ C * (r * D + Real.log (1 / β)) / η ^ 2) →
      ∀ (r D : ℕ) (μl μu η δ : ℝ), 1 ≤ r → 1 ≤ D → 0 < μl → μl ≤ μu → μu ≤ 1 → 0 < η → η < μu →
        0 < δ → δ < 1 →
        (⌈2 * (mA r D (η / (2 * μu)) (δ / 3) : ℝ) / μl + 8 / μl * Real.log (3 / δ) +
            2 / η ^ 2 * Real.log (6 / δ)⌉₊ : ℝ) ≤
          C' * (μu ^ 2 * (r * D + (1 + Real.log (1 / δ))) / (μl * η ^ 2) +
            (1 + Real.log (1 / δ)) / μl + (1 + Real.log (1 / δ)) / η ^ 2) := by sorry

end AgnosticTNS
