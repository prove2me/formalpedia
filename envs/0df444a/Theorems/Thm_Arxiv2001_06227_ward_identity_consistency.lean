-- Prove2me | Theorems.Thm_Arxiv2001_06227_ward_identity_consistency
-- name    : Arxiv2001_06227.ward_identity_consistency
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T08:07:43.398178+00:00
-- url     : https://prove2.me/theorems/33e42d69-4c29-5744-8a46-0f0b6f47efbd
-- title:
--   Eqs. (A1)-(A5): consistency with the Ward identity
-- statement:
--   Let $\widetilde\Sigma,\langle\widetilde G\rangle:\mathbb{R}^3\to\mathbb{C}$, let $\widetilde\Gamma(k,k,k',k')$ be real and symmetric under $k\leftrightarrow k'$ (eq. A3), and let $\langle|E(k)|^2\rangle\ge0$. Assume $k\mapsto\widetilde\Sigma(k)\langle|E(k)|^2\rangle$ is integrable on $\mathbb{R}^3$ and $(k,k')\mapsto\langle\widetilde G^*(k)\rangle\widetilde\Gamma(k,k,k',k')\langle|E(k')|^2\rangle$ is integrable on $\mathbb{R}^3\times\mathbb{R}^3$.
--
--   (i) If (A1) holds,
--   $$\operatorname{Im}\Big[\int\widetilde\Sigma(k)\langle|E(k)|^2\rangle\frac{d^3k}{8\pi^3}+\int\langle\widetilde G^*(k)\rangle\widetilde\Gamma(k,k,k',k')\langle|E(k')|^2\rangle\frac{d^3k}{8\pi^3}\frac{d^3k'}{8\pi^3}\Big]=0,$$
--   then (A4) holds:
--   $$\int\operatorname{Im}\widetilde\Sigma(k)\langle|E(k)|^2\rangle\frac{d^3k}{8\pi^3}=\int\operatorname{Im}\langle\widetilde G(k)\rangle\widetilde\Gamma(k,k,k',k')\langle|E(k')|^2\rangle\frac{d^3k}{8\pi^3}\frac{d^3k'}{8\pi^3}.$$
--
--   (ii) If the Ward identity (A5) holds, $\operatorname{Im}\widetilde\Sigma(k)=\int\operatorname{Im}\langle\widetilde G(k')\rangle\widetilde\Gamma(k,k,k',k')\frac{d^3k'}{8\pi^3}$ for all $k$, then (A4) holds.
--
--   **Formalization Note** $\widetilde\Sigma$, $\langle\widetilde G\rangle$ and $\widetilde\Gamma$ are arbitrary functions with the stated properties; the diagrammatic theory that produces them, and the passage from eq. (37) to (A1) by integration over an unbounded non-absorbing medium, are not formalized. The reality of $\widetilde\Gamma(k,k,k',k')$ in (A3) is encoded by taking it real-valued.
-- source:
--   Sheremet, Pierrat and Carminati, Absorption of scalar waves in correlated disordered media and its maximization using stealth hyperuniformity, arXiv:2001.06227v2 (2020), claim c003; Appendix A, eqs. (A1), (A3), (A4), (A5), PDF p. 10

import Mathlib
import Definitions.Def_Arxiv2001_06227_Basic

open MeasureTheory Filter Topology

namespace Arxiv2001_06227

theorem ward_identity_consistency (sigma green : Space → ℂ) (gamma : Space → Space → ℝ)
    (intensity : Space → ℝ) (hI : ∀ k, 0 ≤ intensity k)
    (hsymm : ∀ k k', gamma k k' = gamma k' k)
    (hsigma : Integrable (fun k => sigma k * (intensity k : ℂ)))
    (hgamma : Integrable (fun q : Space × Space =>
      (starRingEnd ℂ) (green q.1) * (gamma q.1 q.2 : ℂ) * (intensity q.2 : ℂ))
      ((volume : Measure Space).prod volume)) :
    (((∫ k, sigma k * (intensity k : ℂ) / (8 * Real.pi ^ 3 : ℝ)) +
        ∫ k, ∫ k', (starRingEnd ℂ) (green k) * (gamma k k' : ℂ) * (intensity k' : ℂ) /
          ((8 * Real.pi ^ 3) ^ 2 : ℝ)).im = 0 →
      ∫ k, (sigma k).im * intensity k / (8 * Real.pi ^ 3) =
        ∫ k, ∫ k', (green k).im * gamma k k' * intensity k' / (8 * Real.pi ^ 3) ^ 2) ∧
    ((∀ k, (sigma k).im = ∫ k', (green k').im * gamma k k' / (8 * Real.pi ^ 3)) →
      ∫ k, (sigma k).im * intensity k / (8 * Real.pi ^ 3) =
        ∫ k, ∫ k', (green k).im * gamma k k' * intensity k' / (8 * Real.pi ^ 3) ^ 2) := by sorry

end Arxiv2001_06227
