-- Prove2me | Theorems.Thm_CliffordCert_Optimal_Supplement_reference_preserving_support_channel
-- name    : CliffordCert.Optimal.Supplement.reference_preserving_support_channel
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:39:14.848219+00:00
-- url     : https://prove2.me/theorems/ec92ac6c-9a57-484d-9b2d-e5ebd2b23c84
-- title:
--   Lemma 12 — reference-preserving support channel
-- statement:
--   Let $\sigma$ be a density matrix on $\mathbb C^{2^n}$ of any positive rank $k$. Choose an isometry $J:\mathbb C^k\to\mathbb C^{2^n}$ whose range is the support of $\sigma$, and put $P=JJ^\dagger$, $Q=I-P$ and $\sigma_s=J^\dagger\sigma J$. Then the concrete map $\Gamma_\sigma(X)=J^\dagger XJ+\operatorname{Tr}(QX)\sigma_s$ is completely positive and trace preserving on all operators and satisfies $\Gamma_\sigma(\sigma)=\sigma_s$.
--
--   For every ambient state $\rho$ with leakage $p=\operatorname{Tr}(Q\rho)<1$, put $\rho_P=P\rho P/(1-p)$. Then
--
--   $$
--   \|\Gamma_\sigma(\rho)-\sigma_s\|_1
--   =(1-p)\|\rho_P-\sigma\|_1
--   \ge(1-p)\bigl(\|\rho-\sigma\|_1-2\sqrt p\bigr).
--   $$
--
--   For every $0<\varepsilon\le1$, the following implication also holds, without an additional $p<1$ assumption:
--
--   $$
--   \|\rho-\sigma\|_1\ge\varepsilon,\quad p\le\frac{\varepsilon^2}{64}
--   \quad\Longrightarrow\quad
--   \|\Gamma_\sigma(\rho)-\sigma_s\|_1\ge\frac\varepsilon2.
--   $$
--
--   This channel retains the known reference in support coordinates without postselection. The equality and both bounds are the support-reduction guarantees needed by Theorem 5, including alternatives with cross-support coherences.
--
--   Differences from the source:
--   - encoding: choose an isometry J with JJ† equal to the projection onto supp(σ) → J†J=I and range(J)=range(σ), with P defined as JJ†; reason: these are exactly orthonormal coordinates for the support, with k positive and no norm or channel conclusion assumed
--   - encoding: real leakage Tr(Qρ) and normalized compression for p<1 → real part of the trace, with the normalization used only in the p<1 clause; reason: the trace is real on projections and states, and no zero denominator is used
-- source:
--   Hyunho Cha, Jungwoo Lee, STOC 2027 submission #226 (October 2026), pp. 17–18 (PDF 18–19), Lemma 12, Eqs. (30)–(32); source.pdf SHA256 2199cc2ec4c0cc01bfa75380982fe283d38a544dcae40abe5a37198f1a088114

import Definitions.Def_CliffordCert_Optimal_Supplement_support_model
import Definitions.Def_CliffordCert_Optimal_pauli_compression
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace CliffordCert.Optimal.Supplement

/-- Cha–Lee, Lemma 12, pp. 17–18 (PDF 18–19), Eqs. (30)–(32). -/
theorem reference_preserving_support_channel
    {n k : ℕ} (σ : Mat (Bits n)) (hσ : IsState σ)
    (J : Matrix (Bits n) (Fin k) ℂ) (hJ : IsSupportCoordinates σ J) :
    WildeQIT.EntBreaking.IsQuantumChannel (supportChannel σ J) ∧
    supportChannel σ J σ = supportReference σ J ∧
    (∀ ρ : Mat (Bits n), IsState ρ → leakage (supportProjection J) ρ < 1 →
      WildeQIT.traceNorm (supportChannel σ J ρ - supportReference σ J) =
        (1 - leakage (supportProjection J) ρ) *
          WildeQIT.traceNorm (normalizedCompression (supportProjection J) ρ - σ) ∧
      (1 - leakage (supportProjection J) ρ) *
          (WildeQIT.traceNorm (ρ - σ) - 2 * Real.sqrt (leakage (supportProjection J) ρ)) ≤
        WildeQIT.traceNorm (supportChannel σ J ρ - supportReference σ J)) ∧
    (∀ (ρ : Mat (Bits n)) (ε : ℝ), IsState ρ → 0 < ε → ε ≤ 1 →
      ε ≤ WildeQIT.traceNorm (ρ - σ) → leakage (supportProjection J) ρ ≤ ε^2 / 64 →
      ε / 2 ≤ WildeQIT.traceNorm (supportChannel σ J ρ - supportReference σ J)) := by sorry

end CliffordCert.Optimal.Supplement
